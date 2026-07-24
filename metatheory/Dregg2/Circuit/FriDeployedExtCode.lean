/-
# `Dregg2.Circuit.FriDeployedExtCode` — the EXTENSION-TYPED deployed FRI code, and the exact
relation to the base-typed one.

## The gap this closes (two independent lanes hit it)

1. `FriDeepQuotientRlc.lean` (scope note 1) models the deployed DEEP reduction with the committed
   matrix over the BASE field `F` and the reduced word over the EXTENSION `E` — because the
   deployed reduced word IS extension-valued (`fri/src/verifier.rs:617-640` at rev `82cfad73`:
   `ro`/`quotient`/`alpha` are `Challenge`). It records that it CANNOT be wired to `DecodedLdtLink`
   because the in-tree deployed FRI code is base-field typed.
2. `CorrelatedAgreement/Interface.lean` independently concluded the consumer needs correlated
   agreement AT THE QUARTIC EXTENSION, noting the RS code over `L` on the base domain "is
   `extCode` of the base RS".

Nothing in the tree typed the deployed FRI code over the degree-4 extension. This file does, and
proves the relation to the base-typed object rather than assuming it.

## What is PROVEN here

* §1 **THE RELATION (and it is an EQUALITY, not an inclusion).** For any `[Algebra F E]` and any
  `F`-basis `b` of `E`, the RS code over `E` on the EMBEDDED evaluation points is EXACTLY the
  `FriExtChallengeCollapse.extCode` of the base RS code:
  `rsCode_extWord_eq_extCode : ↑(rsCode (extWord E p) D) = extCode b (rsCode p D)`.
  Both directions are proved (`coordWord_mem_rsCode`, `mem_rsCode_of_forall_coordWord`); the
  equality is basis-INDEPENDENT on the left and holds for every basis on the right.
* §2 **What transfers, and what does not.**
  - EMBEDDED BASE WORDS: closeness is the SAME notion at the SAME radius, in BOTH directions
    (`closeN_extWord_iff`). Retyping a base word into the extension neither creates nor destroys
    proximity: `disagree` is literally preserved (`disagree_extWord`), and a base word that is
    `d`-close to the extension code is `d`-close to the BASE code (the nontrivial direction —
    it reads one basis coordinate of the extension codeword and rescales).
  - GENUINELY EXTENSION-VALUED WORDS, forward: `d`-closeness over `E` gives all `[E:F]`
    coordinate words `d`-close over `F` ON ONE COMMON AGREEMENT SET (`coord_closeN_correlated`) —
    extension closeness is a CORRELATED base-closeness, at the same radius, for free.
  - GENUINELY EXTENSION-VALUED WORDS, backward: only with a `[E:F]` factor
    (`closeN_extWord_of_forall_coord`: radius `card r * d`), AND THAT FACTOR IS REAL —
    `coord_close_does_not_transfer_back` exhibits a word all of whose coordinate words are
    `1`-close while the word itself is NOT `1`-close. So "close over `F` coordinatewise" is
    STRICTLY weaker than "close over `E`"; only the forward direction is free.
* §3 **THE DEPLOYED EXTENSION INSTANCE.** `BB4 = GaloisField babyBearP 4` — a genuine degree-4
  extension of BabyBear (`bb4_finrank`, `bb4_card`), CANONICAL: any BabyBear-algebra field of
  cardinality `p^4` — in particular the deployed `BabyBear[X]/(X^4 − 11)` — is
  `≃ₐ[BabyBear]`-isomorphic to it (`deployed_quartic_ext_canonical`), so nothing here depends on
  the binomial presentation (whose irreducibility is a separate numeric fact, NOT proved here).
  `friSetupDeployedExt : FriSetupK BB4 (Fin (8·2^21)) (Fin (2^21)) 8` is the WHOLE deployed FRI
  setup retyped — `friSetupR` turned out to be field-generic, so the folding closure
  (`unfold_closed`/`foldC_mem`) is inherited PROVED, not re-assumed. `friSetupDeployedExt_C` pins
  its code to `friCodeDeployedExt`, and `friCodeDeployedExt_eq_extCode` says that code is exactly
  `extCode bb4Basis friSetupDeployed.C`.
  The unique decoder transports verbatim (`deployedExt_closeN_decode`, same UD radius `7340032`).
* §4 **The `MatrixOracle` vocabulary is already field-generic** — `MatrixOracle`/`ColsClose` carry
  no base-field assumption, so they instantiate at `BB4` with nothing to change. The bridge that
  matters is `deployed_colsClose_ext_iff`: the LITERAL `DecodedLdtLink` antecedent
  `MatrixOracle.ColsClose friSetupDeployed.C 7340032 M` is EQUIVALENT to its extension-typed form
  on the embedded matrix. So moving the consumer to the extension typing is lossless.
* §5 **THE WIRE.** From the literal `DecodedLdtLink` antecedent (base-typed `ColsClose` at the UD
  radius) the deployed extension-valued DEEP-RLC input word is `(numCols · 7340032)`-close to the
  extension-typed deployed DEEP code (`deployed_deep_input_closeN_of_colsClose`), which is the
  `extCode` of the base degree-`< 2^21 − 1` code and sits inside the deployed FRI code
  (`deepCodeDeployedExt_le_friCodeDeployedExt`). This is the connection `FriDeepQuotientRlc`
  scope note 1 says does not exist. ⚠ Read it at its resolution: this is the COMPLETENESS
  direction, and its union-bound radius `numCols · 7340032` is OUTSIDE the unique-decoding regime
  for `numCols ≥ 2` (`deployed_wire_radius_exceeds_ud`) — the converse the consumer needs is
  `RlcDistributes`/CA, still unproved.
* §6 firing + teeth (see below).

## What this does NOT close (the honest remainder for `DecodedLdtLink`)

* The `RlcDistributes` / correlated-agreement hypothesis of `FriDeepQuotientRlc` §5 is untouched:
  this file supplies the TYPING, not the batch→column distribution. `RlcDistributes` is now
  instantiable at `deepCodeDeployedExt` (it is stated over an arbitrary `Submodule E (Fin n → E)`),
  which is exactly what `CorrelatedAgreement/Interface` said the consumer needs — but nobody has
  proved it at those parameters.
* The fold TOWER over the extension code (layers past the first) is not built here; only the
  top-level setup is (its `C'`/fold closure comes with `friSetupR`, but the multi-layer assembly
  is L5/L6 engineering as `FriChainStepIdx`/`DeployedTraceExtract` already name).
* `DecodedLdtLink` itself is a `Prop` about the deployed VERIFIER's transcript; wiring §5 into it
  still needs the verifier-side link (`view`/`AcceptsFull` ⟹ the oracle's rows ARE the opened
  values, and the OOD point/values in the transcript ARE `z`/`vz`) — `DeployedTraceExtract`'s
  named residual, untouched here.
* ⚠ **AND A SECOND, INDEPENDENT FIELD DEFECT ON THE OTHER SIDE OF `DecodedLdtLink` — REPORTED, NOT
  FIXED HERE.** `DecodedLdtLink` (`FriDecodedTraceWitness.lean:456-470`) binds
  `∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)` and evaluates
  `OodColumnLayout.oodBatchResidual d tr ζ qp : Polynomial BabyBear` at `Λ`, with
  `exceptionalSet` a `Finset BabyBear`. In the deployed verifier BOTH of those challenges are
  `Challenge` (the quartic extension): the tree's OWN record of the deployed challenge types says
  so — "the constraint-RLC `α`, the out-of-domain `ζ`, and every commit-phase fold `β` are
  QUARTIC-EXTENSION-FIELD elements" (`ExtFieldChallenge.lean:8-15`, and `singleAirOkExt` takes
  `alpha zeta : ExtElem F` at `extDeg = 4`) — and so are the opened values the residual is built
  from (`z`, `ps_at_z`, `quotient` at `vendor/plonky3-fri-82cfad73/src/verifier.rs:623-640`; the
  FRI batching `alpha : Challenge` at `:143`). A `Polynomial BabyBear` residual cannot represent the
  deployed one, and lane-0 projection is not a homomorphism for products, so the base-typed layout
  equation is a DIFFERENT equation, not a restriction of the deployed one. `TableOpening`'s
  `constraintEval`/`quotientAtZeta`/`vanishingAtZeta : F` are single felts for the same reason
  (the 4-lane opened value squeezed to one lane). Direction of the error: the FS pricing that
  uses `|BabyBear| = 2^31` in place of `|Challenge| ≈ 2^124` is CONSERVATIVE, but the equation
  being at the wrong field is a faithfulness gap in the chain from deployed acceptance to the
  modelled hypothesis. This file supplies what a repair needs (a real `BB4` with `Algebra BabyBear
  BB4`, the code relation, and the lossless `ColsClose` retyping); the retyping of `ζ`/`Λ`/`qp`
  and of `oodBatchResidual`/`exceptionalSet` is NOT done here.
* The `n²`-loss arity cap (`FriDeployedRateInstance` §6) and the FRI soundness floor are
  unchanged; retyping the code changes no soundness bound.

Sorry-free; no `axiom`; no carrier; additive new file; all imports read-only.
`#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Dregg2.Circuit.FriDeepQuotientRlc
import Dregg2.Circuit.FriExtChallengeCollapse
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriDeployedExtCode

open Dregg2.Circuit.FriSoundness (closeN farN disagree mem_disagree closeN_zero_iff_mem)
open Dregg2.Circuit.FriDeployedRateInstance (rsCode mem_rsCode)
open Dregg2.Circuit.FriExtChallengeCollapse (extCode)

/-! ## §1 — The extension retyping, and THE RELATION between the two codes.

The deployed retyping keeps the SAME evaluation domain (the `2^24` two-adic points live in the
base field) and moves only the VALUES into the extension. So the object to build is the RS code
over `E` on the EMBEDDED points `algebraMap ∘ p`, and the question is how it relates to the base
code. The answer (§1.3) is an EQUALITY with `extCode`: a word over `E` is a codeword iff every one
of its `[E:F]` basis-coordinate words is a base codeword. -/

section Generic

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- The retyping of a base-field word (or of the evaluation points) into an extension: the deployed
`Val → Challenge` embedding, which is where the deployed DEEP quotient's mixed typing starts
(`p_at_z - p_at_x` with `p_at_x : Val`). -/
def extWord (E : Type*) [Field E] [Algebra F E] (f : ι → F) : ι → E :=
  fun x => algebraMap F E (f x)

@[simp] theorem extWord_apply (E : Type*) [Field E] [Algebra F E] (f : ι → F) (x : ι) :
    extWord E f x = algebraMap F E (f x) := rfl

variable {E : Type*} [Field E] [Algebra F E]
variable {r : Type*} [Fintype r] [DecidableEq r]

/-- The `i`-th basis-coordinate word of an extension-valued word — the object `extCode` is stated
over (`FriExtChallengeCollapse.extCode` membership is literally `∀ i, coordWord b g i ∈ C`). -/
noncomputable def coordWord (b : Module.Basis r F E) (g : ι → E) (i : r) : ι → F :=
  fun y => b.repr (g y) i

theorem mem_extCode_iff {b : Module.Basis r F E} {C : Submodule F (ι → F)} {g : ι → E} :
    g ∈ extCode b C ↔ ∀ i, coordWord b g i ∈ C := Iff.rfl

/-! ### §1.1 — A base codeword embeds. -/

/-- **The embedding of a base codeword is an extension codeword** (same degree bound, same domain).
The coefficient vector is just embedded. -/
theorem extWord_mem_rsCode {p : ι → F} {D : ℕ} {f : ι → F} (hf : f ∈ rsCode p D) :
    extWord E f ∈ rsCode (extWord E p) D := by
  obtain ⟨c, rfl⟩ := hf
  refine ⟨fun s => algebraMap F E (c s), ?_⟩
  funext x
  simp [extWord, map_sum, map_mul, map_pow]

/-- Constant words are codewords of every positive-degree RS code (used by §2.5 and §6). -/
theorem const_mem_rsCode {q : ι → F} {D : ℕ} (hD : 0 < D) (v : F) :
    (fun _ : ι => v) ∈ rsCode q D := by
  classical
  refine ⟨fun s => if (s : ℕ) = 0 then v else 0, ?_⟩
  funext x
  have h2 : ∑ s : Fin D, (if (s : ℕ) = 0 then v else 0) * q x ^ (s : ℕ) = v := by
    rw [Finset.sum_eq_single (⟨0, hD⟩ : Fin D)]
    · simp
    · intro s _ hs
      have hs0 : (s : ℕ) ≠ 0 := fun h => hs (Fin.ext h)
      simp [hs0]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact h2.symm

/-! ### §1.2 — The two directions of the coordinate characterization. -/

/-- Coordinates of an EXTENSION codeword are BASE codewords: the `i`-th coordinate of the
coefficient vector is a coefficient vector for the base code (the evaluation points are base
scalars, so they pass through `b.repr` as plain multiplications). -/
theorem coordWord_mem_rsCode (b : Module.Basis r F E) {p : ι → F} {D : ℕ} {g : ι → E}
    (hg : g ∈ rsCode (extWord E p) D) (i : r) :
    coordWord b g i ∈ rsCode p D := by
  obtain ⟨c, rfl⟩ := hg
  refine ⟨fun s => b.repr (c s) i, ?_⟩
  funext y
  show b.repr (∑ s : Fin D, c s * (extWord E p y) ^ (s : ℕ)) i
      = ∑ s : Fin D, b.repr (c s) i * p y ^ (s : ℕ)
  rw [map_sum]
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hpow : (extWord E p y) ^ (s : ℕ) = algebraMap F E (p y ^ (s : ℕ)) := by
    simp [extWord, map_pow]
  rw [hpow, mul_comm, ← Algebra.smul_def, map_smul]
  simp [Finsupp.smul_apply, smul_eq_mul, mul_comm]

/-- …and conversely: a word over `E` ALL of whose coordinate words are base codewords IS an
extension codeword. (Reassemble the coefficient vectors along the basis.) -/
theorem mem_rsCode_of_forall_coordWord (b : Module.Basis r F E) {p : ι → F} {D : ℕ} {g : ι → E}
    (h : ∀ i, coordWord b g i ∈ rsCode p D) :
    g ∈ rsCode (extWord E p) D := by
  classical
  choose c hc using h
  refine ⟨fun s => ∑ i : r, c i s • b i, ?_⟩
  funext y
  have hstep : ∀ (s : Fin D) (i : r), (c i s • b i) * (extWord E p y) ^ (s : ℕ)
      = (c i s * p y ^ (s : ℕ)) • b i := by
    intro s i
    have hpow : (extWord E p y) ^ (s : ℕ) = algebraMap F E (p y ^ (s : ℕ)) := by
      simp [extWord, map_pow]
    rw [hpow, smul_mul_assoc, mul_comm (b i), ← Algebra.smul_def, smul_smul]
  calc g y = ∑ i : r, (b.repr (g y) i) • b i := (b.sum_repr (g y)).symm
    _ = ∑ i : r, (∑ s : Fin D, c i s * p y ^ (s : ℕ)) • b i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact congrFun (hc i) y
    _ = ∑ i : r, ∑ s : Fin D, (c i s * p y ^ (s : ℕ)) • b i := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_smul
    _ = ∑ s : Fin D, ∑ i : r, (c i s * p y ^ (s : ℕ)) • b i := Finset.sum_comm
    _ = ∑ s : Fin D, (∑ i : r, c i s • b i) * (extWord E p y) ^ (s : ℕ) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (hstep s i).symm

/-! ### §1.3 — ⚑ THE RELATION. -/

/-- **⚑ THE EXTENSION-TYPED RS CODE IS THE `extCode` OF THE BASE RS CODE** — an EQUALITY, for
every basis of `E/F`. This is the fact `CorrelatedAgreement/Interface.lean:74-75` asserts and
`FriDeepQuotientRlc` scope note 1 needs: retyping the deployed code into the extension adds
exactly the coordinate-wise copies of the base code and nothing else. -/
theorem rsCode_extWord_eq_extCode (b : Module.Basis r F E) (p : ι → F) (D : ℕ) :
    ((rsCode (extWord E p) D : Submodule E (ι → E)) : Set (ι → E)) = extCode b (rsCode p D) := by
  ext g
  exact ⟨fun hg i => coordWord_mem_rsCode b hg i, fun hg => mem_rsCode_of_forall_coordWord b hg⟩

end Generic

/-! ## §2 — Distance: what transfers between the two typings, and what does NOT.

Distance over `E` on the same domain is NOT a priori the same notion as distance over `F`, so this
section proves the transfers rather than assuming them. Three separate facts, with different
strengths — the difference is the whole point:

* embedded BASE words: an EQUIVALENCE at the SAME radius (§2.2) — nothing is gained or lost;
* extension-valued words, FORWARD: `d`-close over `E` ⟹ all coordinate words `d`-close over `F`
  ON ONE COMMON AGREEMENT SET (§2.3) — free, sharp, and correlated;
* extension-valued words, BACKWARD: only with a `[E:F]` factor (§2.4), AND THE FACTOR IS REAL
  (§2.5 exhibits the failure at radius `d`). -/

section Distance

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [Field E] [DecidableEq E] [Algebra F E]
variable {r : Type*} [Fintype r] [DecidableEq r]

/-! ### §2.1 — Two basis facts and the embedded coordinate computation. -/

/-- `1 ≠ 0` in `E`, so `1` has SOME nonzero basis coordinate — the coordinate through which an
embedded base word is read back off. -/
theorem exists_repr_one_ne_zero (b : Module.Basis r F E) : ∃ i, b.repr (1 : E) i ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h0 : b.repr (1 : E) = 0 := by
    ext i; simpa using hcon i
  exact one_ne_zero (b.repr.injective (by rw [h0, map_zero]))

/-- The coordinates of an EMBEDDED base word are that word RESCALED by `1`'s coordinates (the base
scalar passes through `b.repr` as a plain multiplication). -/
theorem coordWord_extWord (b : Module.Basis r F E) (u : ι → F) (i : r) :
    coordWord b (extWord E u) i = fun y => u y * b.repr (1 : E) i := by
  funext y
  show b.repr (algebraMap F E (u y)) i = u y * b.repr (1 : E) i
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  simp [Finsupp.smul_apply, smul_eq_mul]

/-! ### §2.2 — EMBEDDED BASE WORDS: closeness is the SAME notion, at the SAME radius. -/

/-- **`disagree` is literally preserved by the retyping** (`algebraMap` of a field is injective):
the Hamming geometry of base words is untouched by moving them into the extension. -/
theorem disagree_extWord (u v : ι → F) :
    disagree (extWord E u) (extWord E v) = disagree u v := by
  apply Finset.ext
  intro x
  rw [mem_disagree, mem_disagree]
  exact ⟨fun h he => h (congrArg (algebraMap F E) he),
    fun h he => h ((algebraMap F E).injective he)⟩

/-- Forward: a base word `d`-close to the base code embeds to a word `d`-close to the extension
code. -/
theorem closeN_extWord_of_closeN {p : ι → F} {D d : ℕ} {u : ι → F}
    (h : closeN (rsCode p D) d u) : closeN (rsCode (extWord E p) D) d (extWord E u) := by
  obtain ⟨g, hgC, hcard⟩ := h
  exact ⟨extWord E g, extWord_mem_rsCode hgC, by rwa [disagree_extWord]⟩

/-- **The nontrivial direction**: a base word that is `d`-close to the EXTENSION code is `d`-close
to the BASE code — no radius loss. The extension codeword's `i₀`-th coordinate (at a coordinate
where `1` does not vanish), rescaled, is a BASE codeword that agrees wherever the extension
codeword did. So the extension typing cannot make a base word "closer". -/
theorem closeN_of_closeN_extWord (b : Module.Basis r F E) {p : ι → F} {D d : ℕ} {u : ι → F}
    (h : closeN (rsCode (extWord E p) D) d (extWord E u)) : closeN (rsCode p D) d u := by
  classical
  obtain ⟨g, hgC, hcard⟩ := h
  obtain ⟨i₀, hi₀⟩ := exists_repr_one_ne_zero (E := E) b
  refine ⟨(b.repr (1 : E) i₀)⁻¹ • coordWord b g i₀,
    Submodule.smul_mem _ _ (coordWord_mem_rsCode b hgC i₀), ?_⟩
  refine le_trans (Finset.card_le_card ?_) hcard
  intro y hy
  rw [mem_disagree] at hy ⊢
  intro hcon
  apply hy
  have hco : coordWord b (extWord E u) i₀ y = coordWord b g i₀ y := by
    show b.repr (extWord E u y) i₀ = b.repr (g y) i₀
    rw [hcon]
  simp only [coordWord_extWord] at hco
  show u y = ((b.repr (1 : E) i₀)⁻¹ • coordWord b g i₀) y
  simp only [Pi.smul_apply, smul_eq_mul, ← hco]
  field_simp

/-- **⚑ THE EMBEDDED-WORD EQUIVALENCE.** For a BASE word, closeness to the base code and closeness
of its retyping to the extension code are the SAME statement at the SAME radius. This is what makes
retyping the deployed consumer lossless (§4). -/
theorem closeN_extWord_iff (b : Module.Basis r F E) {p : ι → F} {D d : ℕ} {u : ι → F} :
    closeN (rsCode (extWord E p) D) d (extWord E u) ↔ closeN (rsCode p D) d u :=
  ⟨closeN_of_closeN_extWord b, closeN_extWord_of_closeN⟩

/-! ### §2.3 — EXTENSION-VALUED WORDS, forward: closeness over `E` is CORRELATED base closeness. -/

/-- **Closeness over `E` gives ONE agreement set for ALL coordinates.** A `d`-close extension word
has all `[E:F]` of its coordinate words `d`-close to the base code, agreeing off the SAME set of
`≤ d` points. (Correlated agreement of the coordinates comes for free from the extension typing —
it is the batch/RLC direction that needs BCIKS, not this one.) -/
theorem coord_closeN_correlated (b : Module.Basis r F E) {p : ι → F} {D d : ℕ} {g : ι → E}
    (h : closeN (rsCode (extWord E p) D) d g) :
    ∃ T : Finset ι, T.card ≤ d ∧ ∀ i, ∃ w ∈ rsCode p D, disagree (coordWord b g i) w ⊆ T := by
  obtain ⟨h', hmem, hcard⟩ := h
  refine ⟨disagree g h', hcard, fun i => ⟨coordWord b h' i, coordWord_mem_rsCode b hmem i, ?_⟩⟩
  intro y hy
  rw [mem_disagree] at hy ⊢
  intro hcon
  exact hy (by simp [coordWord, hcon])

/-- The per-coordinate form: same radius `d`, no loss. -/
theorem coord_closeN (b : Module.Basis r F E) {p : ι → F} {D d : ℕ} {g : ι → E}
    (h : closeN (rsCode (extWord E p) D) d g) (i : r) :
    closeN (rsCode p D) d (coordWord b g i) := by
  obtain ⟨T, hT, hall⟩ := coord_closeN_correlated b h
  obtain ⟨w, hw, hsub⟩ := hall i
  exact ⟨w, hw, le_trans (Finset.card_le_card hsub) hT⟩

/-! ### §2.4 — EXTENSION-VALUED WORDS, backward: only with a `[E:F]` factor. -/

/-- Coordinatewise closeness lifts back only at radius `[E:F]·d` — a union bound over the
coordinates, whose disagreement sets need not coincide. §2.5 shows this factor is not an artifact
of the proof. -/
theorem closeN_extWord_of_forall_coord (b : Module.Basis r F E) {p : ι → F} {D d : ℕ} {g : ι → E}
    (h : ∀ i, closeN (rsCode p D) d (coordWord b g i)) :
    closeN (rsCode (extWord E p) D) (Fintype.card r * d) g := by
  classical
  choose w hw hcard using h
  refine ⟨fun y => ∑ i : r, w i y • b i, ?_, ?_⟩
  · refine mem_rsCode_of_forall_coordWord b (fun i => ?_)
    have hcoord : coordWord b (fun y => ∑ i : r, w i y • b i) i = w i := by
      funext y
      show b.repr (∑ i' : r, w i' y • b i') i = w i y
      exact congrFun (b.repr_sum_self (fun i' => w i' y)) i
    rw [hcoord]
    exact hw i
  · have hsub : disagree g (fun y => ∑ i : r, w i y • b i)
        ⊆ Finset.univ.biUnion (fun i : r => disagree (coordWord b g i) (w i)) := by
      intro y hy
      rw [mem_disagree] at hy
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      by_contra hcon
      push_neg at hcon
      refine hy ?_
      have hall : ∀ i, b.repr (g y) i = w i y := by
        intro i
        by_contra hne
        exact (hcon i) (mem_disagree.mpr hne)
      calc g y = ∑ i : r, b.repr (g y) i • b i := (b.sum_repr (g y)).symm
        _ = ∑ i : r, w i y • b i := Finset.sum_congr rfl fun i _ => by rw [hall i]
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc ∑ i : r, (disagree (coordWord b g i) (w i)).card
        ≤ ∑ _i : r, d := Finset.sum_le_sum fun i _ => hcard i
      _ = Fintype.card r * d := by simp [Finset.sum_const, Finset.card_univ, mul_comm]

/-! ### §2.5 — ⚑ TEETH: the `[E:F]` factor is REAL — the backward direction FAILS at radius `d`. -/

/-- A word that agrees with a codeword off a single point is `1`-close. -/
theorem closeN_one_of_agree_off_point {C : Submodule F (ι → F)} {f w : ι → F} (hw : w ∈ C)
    {y₀ : ι} (h : ∀ y, y ≠ y₀ → f y = w y) : closeN C 1 f := by
  classical
  refine ⟨w, hw, ?_⟩
  have hsub : disagree f w ⊆ {y₀} := by
    intro y hy
    rw [mem_disagree] at hy
    simp only [Finset.mem_singleton]
    by_contra hne
    exact hy (h y hne)
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- **⚑ THE BACKWARD DIRECTION GENUINELY LOSES THE `[E:F]` FACTOR.** On a `3`-point domain with the
constants code, the word `(0, b i₀, b i₁)` has EVERY coordinate word `1`-close to the base code
(each coordinate is supported at one point), yet the word itself is NOT `1`-close to the extension
code — its three values are pairwise distinct, so no constant can agree at two points. So
"every coordinate is `d`-close over `F`" is STRICTLY WEAKER than "`d`-close over `E`", and §2.3's
free forward transfer has no converse at the same radius. -/
theorem coord_close_does_not_transfer_back (b : Module.Basis r F E) {i₀ i₁ : r} (hne : i₀ ≠ i₁)
    (q : Fin 3 → F) :
    ∃ g : Fin 3 → E,
      (∀ i, closeN (rsCode q 1) 1 (coordWord b g i)) ∧
      ¬ closeN (rsCode (extWord E q) 1) 1 g := by
  refine ⟨![0, b i₀, b i₁], ?_, ?_⟩
  · intro i
    by_cases h0 : i₀ = i
    · refine closeN_one_of_agree_off_point (C := rsCode q 1) (Submodule.zero_mem _)
        (y₀ := (1 : Fin 3)) ?_
      intro y hy
      fin_cases y
      · simp [coordWord]
      · exact absurd rfl hy
      · have : i₁ ≠ i := fun h => hne (h0.trans h.symm)
        simp [coordWord, this]
    · by_cases h1 : i₁ = i
      · refine closeN_one_of_agree_off_point (C := rsCode q 1) (Submodule.zero_mem _)
          (y₀ := (2 : Fin 3)) ?_
        intro y hy
        fin_cases y
        · simp [coordWord]
        · simp [coordWord, h0]
        · exact absurd rfl hy
      · refine closeN_one_of_agree_off_point (C := rsCode q 1) (Submodule.zero_mem _)
          (y₀ := (0 : Fin 3)) ?_
        intro y _
        fin_cases y <;> simp [coordWord, h0, h1]
  · rintro ⟨w, hwC, hcard⟩
    obtain ⟨c, rfl⟩ := hwC
    -- the codeword is a CONSTANT
    have hconst : ∀ x : Fin 3, (∑ s : Fin 1, c s * (extWord E q x) ^ (s : ℕ)) = c 0 := by
      intro x
      simp
    -- the three values are pairwise distinct
    have hpair : ∀ x y : Fin 3, x ≠ y →
        (![0, b i₀, b i₁] : Fin 3 → E) x ≠ (![0, b i₀, b i₁] : Fin 3 → E) y := by
      have hb0 : b i₀ ≠ 0 := b.ne_zero i₀
      have hb1 : b i₁ ≠ 0 := b.ne_zero i₁
      have hbb : b i₀ ≠ b i₁ := fun h => hne (b.injective h)
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [eq_comm, Ne.symm]
    -- at most one point can agree with a constant, so at least two disagree
    set A : Finset (Fin 3) := Finset.univ.filter
      (fun x => (![0, b i₀, b i₁] : Fin 3 → E) x
        = (fun x => ∑ s : Fin 1, c s * (extWord E q x) ^ (s : ℕ)) x) with hA
    have hAle : A.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      by_contra hxy
      refine hpair x y hxy ?_
      rw [hA, Finset.mem_filter] at hx hy
      rw [hx.2, hy.2]
      simp only [hconst]
    have hsplit : A.card + (disagree (![0, b i₀, b i₁] : Fin 3 → E)
        (fun x => ∑ s : Fin 1, c s * (extWord E q x) ^ (s : ℕ))).card = 3 := by
      rw [hA]
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin 3)))
        (p := fun x => (![0, b i₀, b i₁] : Fin 3 → E) x
          = (fun x => ∑ s : Fin 1, c s * (extWord E q x) ^ (s : ℕ)) x)
      simpa [disagree, Finset.card_univ] using this
    have hcard' : (disagree (![0, b i₀, b i₁] : Fin 3 → E)
        (fun x => ∑ s : Fin 1, c s * (extWord E q x) ^ (s : ℕ))).card ≤ 1 := hcard
    omega

end Distance

/-! ## §2.6 — RS codes are nested (needed because the DEEP quotient code is ONE degree lower). -/

/-- Degree-monotonicity of the RS code: pad the coefficient vector with zeros. The deployed FRI
input word lives in the degree-`< k−1` code (`FriDeepQuotientRlc.rlcQuotPoly_natDegree_lt`), which
this places INSIDE the deployed degree-`< k` code. -/
theorem rsCode_mono {F : Type*} [Field F] {ι : Type*} [Fintype ι] {p : ι → F} {D D' : ℕ}
    (h : D ≤ D') : rsCode p D ≤ rsCode p D' := by
  classical
  rintro f ⟨c, rfl⟩
  refine ⟨fun s => if hs : (s : ℕ) < D then c ⟨(s : ℕ), hs⟩ else 0, ?_⟩
  funext x
  set e : ℕ → F := fun s => (if hs : s < D then c ⟨s, hs⟩ else 0) * p x ^ s with he
  have h1 : ∑ s : Fin D, c s * p x ^ (s : ℕ) = ∑ s ∈ Finset.range D, e s := by
    rw [← Fin.sum_univ_eq_sum_range e D]
    exact Finset.sum_congr rfl fun s _ => by simp [he, s.isLt]
  have h2 : ∑ s : Fin D', (if hs : (s : ℕ) < D then c ⟨(s : ℕ), hs⟩ else 0) * p x ^ (s : ℕ)
      = ∑ s ∈ Finset.range D', e s := Fin.sum_univ_eq_sum_range e D'
  have hrange : Finset.range D ⊆ Finset.range D' := Finset.range_mono h
  have h3 : ∑ s ∈ Finset.range D, e s = ∑ s ∈ Finset.range D', e s := by
    refine Finset.sum_subset hrange fun s _ hns => ?_
    have hsD : ¬ s < D := by simpa using hns
    simp [he, hsD]
  show ∑ s : Fin D, c s * p x ^ (s : ℕ)
      = ∑ s : Fin D', (if hs : (s : ℕ) < D then c ⟨(s : ℕ), hs⟩ else 0) * p x ^ (s : ℕ)
  rw [h1, h3, ← h2]

/-! ## §3 — ⚑ THE DEPLOYED EXTENSION INSTANCE.

The deployed `Challenge` field is `BinomialExtensionField<BabyBear, 4>` = `BabyBear[X]/(X^4 − 11)`
(`p3-baby-bear/src/baby_bear.rs:66`, `W = 11`; `ExtFieldChallenge.deployed_extDeg_four`). Proving
`X^4 − 11` irreducible over BabyBear is a separate numeric fact NOT established here — and it is
not needed: every degree-4 extension of BabyBear is the SAME field up to a BabyBear-algebra
isomorphism (§3.1), so the deployed quartic extension is (isomorphic to) `GaloisField p 4`, which
Mathlib gives us as a genuine `Field` with a genuine `Algebra BabyBear` structure. Everything below
is therefore about the deployed object, stated at the resolution the tree can actually prove. -/

section Deployed

open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.FriDeployedRateInstance
  (pR friSetupR friSetupDeployed omega24 omega24_ne omega24_fiber_inj omega24_pow_domain
   pR_deployed_inj)
open Dregg2.Circuit.FriFoldArity (FriSetupK)

/-- **The deployed quartic extension**, as a Lean field. -/
abbrev BB4 : Type := GaloisField babyBearP 4

noncomputable instance instDecidableEqBB4 : DecidableEq BB4 := Classical.decEq _
noncomputable instance instFintypeBB4 : Fintype BB4 := Fintype.ofFinite _

/-! ### §3.1 — It is a genuine degree-4 extension, and it is THE deployed one. -/

/-- `[BB4 : BabyBear] = 4` — the deployed `extDeg`. -/
theorem bb4_finrank : Module.finrank BabyBear BB4 = 4 :=
  GaloisField.finrank babyBearP (by norm_num)

/-- `|BB4| = p^4 ≈ 2^124` — the deployed challenge space (`CorrelatedAgreement/Interface`'s
`|R| ≈ 2^123.6`). -/
theorem bb4_card : Fintype.card BB4 = babyBearP ^ 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card babyBearP 4 (by norm_num)

/-- **⚑ CANONICITY — this IS the deployed extension.** Any field that is a BabyBear-algebra of
cardinality `p^4` — in particular the deployed `BabyBear[X]/(X^4 − 11)`, whatever presentation is
used — is BabyBear-algebra isomorphic to `BB4`. So nothing below depends on the binomial
presentation (whose irreducibility is not proved in this tree). -/
theorem deployed_quartic_ext_canonical (L : Type) [Field L] [Fintype L] [Algebra BabyBear L]
    (hcard : Fintype.card L = babyBearP ^ 4) : Nonempty (L ≃ₐ[BabyBear] BB4) :=
  ⟨FiniteField.algEquivOfCardEq babyBearP (by rw [hcard, bb4_card])⟩

/-- A basis of the deployed extension over BabyBear — the four `Val` lanes of a `Challenge`. -/
noncomputable def bb4Basis : Module.Basis (Fin 4) BabyBear BB4 :=
  Module.finBasisOfFinrankEq BabyBear BB4 bb4_finrank

/-! ### §3.2 — The deployed FRI setup, retyped. `friSetupR` is field-generic, so the FOLDING
CLOSURE (`unfold_closed`/`foldC_mem`) is inherited PROVED — not re-assumed. -/

/-- The deployed `2^24`-th root of unity, retyped into the extension. -/
noncomputable def omega24Ext : BB4 := algebraMap BabyBear BB4 omega24

theorem omega24Ext_ne : omega24Ext ≠ 0 := by
  intro h
  apply omega24_ne
  apply (algebraMap BabyBear BB4).injective
  rw [map_zero]
  exact h

theorem omega24Ext_fiber_inj :
    Function.Injective (fun i : Fin 8 => (omega24Ext ^ (2 ^ 21)) ^ (i : ℕ)) := by
  have hmap : ∀ i : Fin 8, (omega24Ext ^ (2 ^ 21)) ^ (i : ℕ)
      = algebraMap BabyBear BB4 ((omega24 ^ (2 ^ 21)) ^ (i : ℕ)) := by
    intro i; simp [omega24Ext, map_pow]
  intro i j h
  have h' : (omega24Ext ^ (2 ^ 21)) ^ (i : ℕ) = (omega24Ext ^ (2 ^ 21)) ^ (j : ℕ) := h
  rw [hmap i, hmap j] at h'
  exact omega24_fiber_inj ((algebraMap BabyBear BB4).injective h')

theorem omega24Ext_pow_domain : omega24Ext ^ (8 * 2 ^ 21) = 1 := by
  rw [omega24Ext, ← map_pow, omega24_pow_domain, map_one]

/-- **⚑ THE EXTENSION-TYPED DEPLOYED FRI SETUP** — `|L| = 2^24`, arity `8`, `|L^8| = 2^21`, domain
code degree `< 2^21` (rate `1/8`), folded code degree `< 2^18` (rate `1/8`), over the QUARTIC
EXTENSION. Same domain, same rate, same arity as `friSetupDeployed`; only the value field moved.
The folding closure is `friSetupR`'s, proved generically in the field. -/
noncomputable def friSetupDeployedExt :
    FriSetupK BB4 (Fin (8 * 2 ^ 21)) (Fin (2 ^ 21)) 8 :=
  friSetupR 8 (2 ^ 21) (2 ^ 18) (by norm_num) omega24Ext omega24Ext_ne omega24Ext_fiber_inj
    omega24Ext_pow_domain

/-! ### §3.3 — The extension-typed deployed CODE, and its relation to the base-typed one. -/

/-- The deployed evaluation domain, retyped (the SAME `2^24` points, embedded). -/
noncomputable def deployedPtsExt : Fin (8 * 2 ^ 21) → BB4 := extWord BB4 (pR 8 (2 ^ 21) omega24)

theorem pR_omega24Ext_eq : pR 8 (2 ^ 21) omega24Ext = deployedPtsExt := by
  funext x
  show omega24Ext ^ (x : ℕ) = algebraMap BabyBear BB4 (omega24 ^ (x : ℕ))
  rw [omega24Ext, ← map_pow]

/-- **⚑ THE EXTENSION-TYPED DEPLOYED FRI CODE** — the object the tree did not have. -/
noncomputable def friCodeDeployedExt : Submodule BB4 (Fin (8 * 2 ^ 21) → BB4) :=
  rsCode deployedPtsExt (2 ^ 18 * 8)

/-- …and it IS the code of the retyped setup. -/
theorem friSetupDeployedExt_C : friSetupDeployedExt.C = friCodeDeployedExt := by
  show rsCode (pR 8 (2 ^ 21) omega24Ext) (2 ^ 18 * 8) = friCodeDeployedExt
  rw [pR_omega24Ext_eq]
  rfl

/-- **⚑⚑ THE RELATION AT THE DEPLOYED INSTANCE**: the extension-typed deployed FRI code is EXACTLY
the `extCode` of `friSetupDeployed.C`. This is the statement `FriDeepQuotientRlc` scope note 1 and
`CorrelatedAgreement/Interface.lean:74-75` both needed and neither had. -/
theorem friCodeDeployedExt_eq_extCode :
    (friCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) = extCode bb4Basis friSetupDeployed.C :=
  rsCode_extWord_eq_extCode bb4Basis (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8)

/-- The DEEP-quotient input code: degree `< 2^21 − 1`, ONE degree below the committed code
(`FriDeepQuotientRlc.rlcQuotPoly_natDegree_lt`), on the same retyped domain. -/
noncomputable def deepCodeDeployedExt : Submodule BB4 (Fin (8 * 2 ^ 21) → BB4) :=
  rsCode deployedPtsExt (2 ^ 18 * 8 - 1)

/-- The DEEP code is likewise the `extCode` of a base-field RS code (one degree lower). -/
theorem deepCodeDeployedExt_eq_extCode :
    (deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4))
      = extCode bb4Basis (rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8 - 1)) :=
  rsCode_extWord_eq_extCode bb4Basis (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8 - 1)

/-- **The DEEP code sits INSIDE the deployed FRI code** — so proximity to the quotient code is
proximity to the deployed code, at the same radius. -/
theorem deepCodeDeployedExt_le_friCodeDeployedExt :
    deepCodeDeployedExt ≤ friCodeDeployedExt :=
  rsCode_mono (by norm_num)

/-! ### §3.4 — The unique decoder transports verbatim (same domain, degree, radius). -/

theorem deployedPtsExt_inj : Function.Injective deployedPtsExt :=
  fun _ _ h => pR_deployed_inj ((algebraMap BabyBear BB4).injective h)

/-- **The deployed UD decode, at the extension typing.** Same `2^24` domain, same degree-`2^21`
code, same unique-decoding radius `7340032` as `FriCloseNUniqueDecode`'s base-field statement:
retyping the values changes no decoding parameter. -/
theorem deployedExt_closeN_decode {f : Fin (8 * 2 ^ 21) → BB4}
    (hclose : closeN friCodeDeployedExt 7340032 f) :
    ∃! g : Fin (8 * 2 ^ 21) → BB4, g ∈ friCodeDeployedExt ∧ (disagree f g).card ≤ 7340032 :=
  Dregg2.Circuit.FriCloseNUniqueDecode.closeN_rsCode_decode deployedPtsExt_inj hclose
    (by norm_num)

end Deployed

/-! ## §4 — The `MatrixOracle` vocabulary at the extension typing.

`FriBatchedOracle.MatrixOracle` is `ι → Fin c → F` with NO field assumption, and `ColsClose` needs
only `[Field F] [DecidableEq F]`. So the batched-oracle vocabulary `DecodedLdtLink` speaks is
ALREADY field-generic — there is nothing to redefine, only to instantiate. What has to be PROVED is
the bridge: that the base-typed antecedent and its extension-typed form are the same statement. -/

section Oracle

open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : Type*} [Fintype r] [DecidableEq r]
variable {c : ℕ}

/-- The committed matrix, retyped into the extension — the deployed `Val → Challenge` embedding
applied entrywise (`p_at_x` entering the DEEP quotient). -/
def extMatrix (E : Type*) [Field E] [Algebra F E] (M : MatrixOracle ι c F) : MatrixOracle ι c E :=
  fun x j => algebraMap F E (M x j)

@[simp] theorem extMatrix_col (E : Type*) [Field E] [Algebra F E] (M : MatrixOracle ι c F)
    (j : Fin c) : (extMatrix E M).col j = extWord E (M.col j) := rfl

variable {E : Type*} [Field E] [DecidableEq E] [Algebra F E]

/-- **The multi-column proximity input is the SAME statement in both typings** — every column is a
base word, and §2.2 says base words keep their distance exactly. -/
theorem colsClose_extMatrix_iff (b : Module.Basis r F E) {p : ι → F} {D d : ℕ}
    (M : MatrixOracle ι c F) :
    MatrixOracle.ColsClose (rsCode (extWord E p) D) d (extMatrix E M)
      ↔ MatrixOracle.ColsClose (rsCode p D) d M := by
  constructor
  · intro h j
    exact closeN_of_closeN_extWord b (by simpa using h j)
  · intro h j
    simpa using closeN_extWord_of_closeN (E := E) (h j)

end Oracle

section DeployedOracle

open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (pR friSetupDeployed omega24)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.FriCloseNUniqueDecode (mem_rsCode_iff_lowDegree_evalVec)
open Dregg2.Circuit.FriDeepQuotientRlc (friInputWord friInputWord_closeN)

/-- **⚑ THE CONSUMER BRIDGE.** The LITERAL `DecodedLdtLink` antecedent
(`MatrixOracle.ColsClose friSetupDeployed.C 7340032`, `FriDecodedTraceWitness.lean:461`) is
EQUIVALENT to its extension-typed form on the retyped matrix. Moving the consumer to the extension
typing is therefore lossless — it neither weakens nor strengthens the hypothesis. -/
theorem deployed_colsClose_ext_iff {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) :
    MatrixOracle.ColsClose friCodeDeployedExt 7340032 (extMatrix BB4 M)
      ↔ MatrixOracle.ColsClose friSetupDeployed.C 7340032 M :=
  colsClose_extMatrix_iff bb4Basis M

/-- The extension-valued reduced word, spoken in the SAME `MatrixOracle` vocabulary: a one-column
extension matrix, whose `ColsClose` IS the word's `closeN` (`FriBatchedOracle`'s `c = 1` bridge,
field-generic — instantiated here at the extension). -/
theorem deployed_colsClose_ofWord_iff (f : Fin (8 * 2 ^ 21) → BB4) (d : ℕ) :
    MatrixOracle.ColsClose deepCodeDeployedExt d (MatrixOracle.ofWord f)
      ↔ closeN deepCodeDeployedExt d f :=
  MatrixOracle.colsClose_ofWord_iff _ _ _

/-! ## §5 — ⚑ THE WIRE: from the literal `DecodedLdtLink` antecedent to the deployed
extension-valued DEEP-RLC input word. -/

/-- The interpolants hidden in the `ColsClose` antecedent: each committed column is `7340032`-close
to the evaluation of a genuine degree-`< 2^21` polynomial (`mem_rsCode_iff_lowDegree_evalVec`). -/
theorem colsClose_interpolants {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (h : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M) :
    ∃ p : Fin numCols → Polynomial BabyBear,
      (∀ j, (p j).natDegree < 2 ^ 18 * 8) ∧
      (∀ j, (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) (p j))).card ≤ 7340032) := by
  classical
  have hj : ∀ j : Fin numCols, ∃ q : Polynomial BabyBear, q.natDegree < 2 ^ 18 * 8 ∧
      (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) q)).card ≤ 7340032 := by
    intro j
    obtain ⟨g, hgC, hcard⟩ := h j
    have hgC' : g ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hgC
    obtain ⟨q, hqdeg, rfl⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hgC'
    exact ⟨q, hqdeg, hcard⟩
  choose p hdeg hclose using hj
  exact ⟨p, hdeg, hclose⟩

/-- **The deployed DEEP-RLC input word lands in the EXTENSION-TYPED deployed quotient code.**
`FriDeepQuotientRlc.friInputWord_closeN` instantiated at the deployed parameters: committed columns
`7340032`-close to degree-`< 2^21` codewords and honest OOD values put the extension-valued reduced
word `(numCols · 7340032)`-close to `deepCodeDeployedExt`. -/
theorem deployed_deep_input_closeN {numCols : ℕ} (α z : BB4)
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) (vz : Fin numCols → BB4)
    (p : Fin numCols → Polynomial BabyBear)
    (hz : ∀ x, deployedPtsExt x ≠ z)
    (hdeg : ∀ j, (p j).natDegree < 2 ^ 18 * 8)
    (hclose : ∀ j, (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) (p j))).card ≤ 7340032)
    (hood : ∀ j, vz j = ((p j).map (algebraMap BabyBear BB4)).eval z) :
    closeN deepCodeDeployedExt (numCols * 7340032)
      (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz) :=
  friInputWord_closeN (k := 2 ^ 18 * 8) _ α z M vz p hz hclose hood hdeg (by norm_num)

/-- **⚑⚑ THE WIRE, from the LITERAL antecedent.** Given exactly what `DecodedLdtLink` assumes —
`MatrixOracle.ColsClose friSetupDeployed.C 7340032 M` — and a valid out-of-domain point, the
deployed extension-valued FRI input word for the HONEST OOD values is `(numCols · 7340032)`-close
to the extension-typed deployed DEEP code, hence to the extension-typed deployed FRI code. This is
the connection `FriDeepQuotientRlc` scope note 1 records as not existing in the tree. -/
theorem deployed_deep_input_closeN_of_colsClose {numCols : ℕ} (α z : BB4)
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M)
    (hz : ∀ x, deployedPtsExt x ≠ z) :
    ∃ vz : Fin numCols → BB4,
      closeN deepCodeDeployedExt (numCols * 7340032)
        (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz) ∧
      closeN friCodeDeployedExt (numCols * 7340032)
        (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz) := by
  obtain ⟨p, hdeg, hclose⟩ := colsClose_interpolants M hcols
  refine ⟨fun j => ((p j).map (algebraMap BabyBear BB4)).eval z, ?_, ?_⟩
  · exact deployed_deep_input_closeN α z M _ p hz hdeg hclose (fun _ => rfl)
  · obtain ⟨g, hgC, hcard⟩ := deployed_deep_input_closeN α z M _ p hz hdeg hclose (fun _ => rfl)
    exact ⟨g, deepCodeDeployedExt_le_friCodeDeployedExt hgC, hcard⟩

/-- **The reduced word's four BabyBear lanes are each close to the BASE code, on ONE common
agreement set** (§2.3 at the deployed instance). So the extension typing does not leave the base
decode behind: the base-field decode still receives base-field columns, through the coordinate
projection — exactly as `CorrelatedAgreement/Interface.lean:74-76` describes. -/
theorem deployed_deep_input_coords_close {numCols : ℕ} (α z : BB4)
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M)
    (hz : ∀ x, deployedPtsExt x ≠ z) :
    ∃ vz : Fin numCols → BB4, ∃ T : Finset (Fin (8 * 2 ^ 21)), T.card ≤ numCols * 7340032 ∧
      ∀ i : Fin 4, ∃ w ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8 - 1),
        disagree (coordWord bb4Basis
          (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz) i) w ⊆ T := by
  obtain ⟨vz, hdeep, -⟩ := deployed_deep_input_closeN_of_colsClose α z M hcols hz
  exact ⟨vz, coord_closeN_correlated bb4Basis hdeep⟩

/-- ⚠ **HONEST BOOKKEEPING — §5's union-bound radius LEAVES the unique-decoding regime as soon as
there is more than one committed column.** `numCols · 7340032 > 7340032` for `numCols ≥ 2`, so
`deployedExt_closeN_decode` does NOT apply to the reduced word at §5's radius. §5 is the
COMPLETENESS direction (columns close ⟹ reduced word close); what the consumer needs is the
CONVERSE (reduced word close ⟹ every column close AT the UD radius), and that converse is exactly
`FriDeepQuotientRlc.RlcDistributes` / BCIKS correlated agreement — unproved at these parameters.
Nothing here should be read as decoding the reduced word. -/
theorem deployed_wire_radius_exceeds_ud {numCols : ℕ} (h : 2 ≤ numCols) :
    7340032 < numCols * 7340032 := by
  have hle : 2 * 7340032 ≤ numCols * 7340032 := Nat.mul_le_mul_right _ h
  omega

end DeployedOracle

/-! ## §6 — FIRING (the definitions are non-vacuous) and TEETH.

The retyping would be decoration if the extension code were just the base code in disguise. It is
not: §6.1 shows a nontrivial extension always has code words NO base word maps to, and §6.2/§6.3
fire that at the DEPLOYED quartic extension and at a SMALL genuine one (`F₄` over `F₂`), alongside
the base-codeword embedding and the §2.5 failure of the backward transfer. -/

section Fire

open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriDeployedRateInstance (pR omega24)

/-! ### §6.1 — A nontrivial extension is not reached by the embedding. -/

/-- If `[E:F] > 1` then `algebraMap` is not surjective: were it, it would be an `F`-linear
equivalence and force `[E:F] = 1`. -/
theorem exists_not_mem_range_algebraMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (h : 1 < Module.finrank F E) : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective (Algebra.linearMap F E) := fun a b hab =>
    (algebraMap F E).injective hab
  have hsurj : Function.Surjective (Algebra.linearMap F E) := by
    intro x
    obtain ⟨y, hy⟩ := hcon x
    exact ⟨y, hy⟩
  have hrank : Module.finrank F F = Module.finrank F E :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_self] at hrank
  omega

/-- **The extension-typed code contains words that are the retyping of NO base word.** (Take a
constant at a scalar outside the image; constants are codewords at any positive degree.) -/
theorem extCode_beyond_base_image {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι : Type*} [Fintype ι] {p : ι → F} {D : ℕ} (hD : 0 < D) (y₀ : ι)
    (h : 1 < Module.finrank F E) :
    ∃ g : ι → E, g ∈ rsCode (extWord E p) D ∧ ∀ f : ι → F, extWord E f ≠ g := by
  obtain ⟨x, hx⟩ := exists_not_mem_range_algebraMap (F := F) (E := E) h
  refine ⟨fun _ => x, const_mem_rsCode hD x, ?_⟩
  intro f hf
  exact hx ⟨f y₀, congrFun hf y₀⟩

/-! ### §6.2 — FIRING at the DEPLOYED quartic extension. -/

/-- A base codeword's retyping IS a codeword of the extension-typed DEPLOYED code. -/
theorem fire_deployed_base_codeword_embeds :
    extWord BB4 ((fun _ => 1) : Fin (8 * 2 ^ 21) → BabyBear) ∈ friCodeDeployedExt :=
  extWord_mem_rsCode (const_mem_rsCode (by norm_num) 1)

/-- **⚑ THE RETYPING IS NOT DECORATION.** The extension-typed deployed code contains words that are
NOT the retyping of ANY BabyBear word — `[BB4 : BabyBear] = 4 > 1`. This is exactly the situation
the deployed DEEP reduction is in (`ro : Challenge` over a `Val` domain), and the reason a
base-typed code could not host it. -/
theorem fire_deployed_ext_word_beyond_base :
    ∃ g : Fin (8 * 2 ^ 21) → BB4, g ∈ friCodeDeployedExt ∧
      ∀ f : Fin (8 * 2 ^ 21) → BabyBear, extWord BB4 f ≠ g :=
  extCode_beyond_base_image (by norm_num) ⟨0, by norm_num⟩ (by rw [bb4_finrank]; norm_num)

/-- **§2.5 TEETH at the DEPLOYED quartic basis**: four lanes each `1`-close to the base code, the
word itself not `1`-close over the extension. -/
theorem fire_deployed_backward_failure (q : Fin 3 → BabyBear) :
    ∃ g : Fin 3 → BB4,
      (∀ i, closeN (rsCode q 1) 1 (coordWord bb4Basis g i)) ∧
      ¬ closeN (rsCode (extWord BB4 q) 1) 1 g :=
  coord_close_does_not_transfer_back bb4Basis (show (0 : Fin 4) ≠ 1 by decide) q

/-- **NON-VACUITY OF §5's HYPOTHESIS BUNDLE.** An out-of-domain challenge EXISTS (every domain
point is in the image of the base field, so any non-base `z` is automatically outside the
evaluation domain — and the deployed `zeta` IS drawn from the extension), and the `ColsClose`
antecedent is inhabited by a genuinely codeword-valued commitment. So
`deployed_deep_input_closeN_of_colsClose` is not true by emptiness. -/
theorem fire_deployed_wire_hypotheses_inhabited (numCols : ℕ) :
    ∃ (z : BB4) (M : Dregg2.Circuit.FriBatchedOracle.MatrixOracle
        (Fin (8 * 2 ^ 21)) numCols BabyBear),
      (∀ x, deployedPtsExt x ≠ z) ∧
      Dregg2.Circuit.FriBatchedOracle.MatrixOracle.ColsClose
        Dregg2.Circuit.FriDeployedRateInstance.friSetupDeployed.C 7340032 M := by
  obtain ⟨z, hz⟩ := exists_not_mem_range_algebraMap (F := BabyBear) (E := BB4)
    (by rw [bb4_finrank]; norm_num)
  refine ⟨z, (fun _ _ => 1), fun x hx => hz ⟨_, hx⟩, ?_⟩
  exact Dregg2.Circuit.FriBatchedOracle.MatrixOracle.colsClose_of_forall_mem
    (fun _ => const_mem_rsCode (by norm_num) 1) _

/-! ### §6.3 — FIRING at a SMALL genuine extension: `F₄ = GaloisField 2 2` over `F₂`. -/

/-- The small base field. -/
abbrev F2 : Type := ZMod 2

/-- A small GENUINE extension (degree 2). -/
abbrev F4 : Type := GaloisField 2 2

noncomputable instance instDecidableEqF4 : DecidableEq F4 := Classical.decEq _

theorem f4_finrank : Module.finrank F2 F4 = 2 := GaloisField.finrank 2 (by norm_num)

noncomputable def f4Basis : Module.Basis (Fin 2) F2 F4 :=
  Module.finBasisOfFinrankEq F2 F4 f4_finrank

/-- A 3-point demo domain over `F₂`. -/
def smallPts : Fin 3 → F2 := ![0, 1, 0]

/-- FIRE: the base codeword `1` embeds into the extension code. -/
theorem fire_small_base_codeword_embeds :
    extWord F4 ((fun _ => 1) : Fin 3 → F2) ∈ rsCode (extWord F4 smallPts) 1 :=
  extWord_mem_rsCode (const_mem_rsCode (by norm_num) 1)

/-- FIRE: and the extension code has a word beyond every base word's retyping. -/
theorem fire_small_ext_word_beyond_base :
    ∃ g : Fin 3 → F4, g ∈ rsCode (extWord F4 smallPts) 1 ∧
      ∀ f : Fin 3 → F2, extWord F4 f ≠ g :=
  extCode_beyond_base_image (by norm_num) 0 (by rw [f4_finrank]; norm_num)

/-- FIRE: §1.3's relation, on the small instance (whose two sides §6.3 has just shown are
inhabited by BOTH an embedded base codeword and a word beyond the base image). -/
theorem fire_small_relation :
    ((rsCode (extWord F4 smallPts) 1 : Submodule F4 (Fin 3 → F4)) : Set (Fin 3 → F4))
      = extCode f4Basis (rsCode smallPts 1) :=
  rsCode_extWord_eq_extCode f4Basis smallPts 1

/-- TEETH at the small instance: coordinatewise `1`-closeness over `F₂` does NOT give `1`-closeness
over `F₄`. -/
theorem fire_small_backward_failure :
    ∃ g : Fin 3 → F4,
      (∀ i, closeN (rsCode smallPts 1) 1 (coordWord f4Basis g i)) ∧
      ¬ closeN (rsCode (extWord F4 smallPts) 1) 1 g :=
  coord_close_does_not_transfer_back f4Basis (show (0 : Fin 2) ≠ 1 by decide) smallPts

end Fire

/-! ## §7 — Axiom hygiene. -/

#assert_all_clean [
  extWord_mem_rsCode,
  coordWord_mem_rsCode,
  mem_rsCode_of_forall_coordWord,
  rsCode_extWord_eq_extCode,
  exists_repr_one_ne_zero,
  coordWord_extWord,
  disagree_extWord,
  closeN_extWord_of_closeN,
  closeN_of_closeN_extWord,
  closeN_extWord_iff,
  coord_closeN_correlated,
  coord_closeN,
  closeN_extWord_of_forall_coord,
  const_mem_rsCode,
  coord_close_does_not_transfer_back,
  rsCode_mono
]

#assert_all_clean [
  friSetupDeployedExt,
  friCodeDeployedExt,
  deepCodeDeployedExt,
  bb4Basis,
  deployedPtsExt,
  bb4_finrank,
  bb4_card,
  deployed_quartic_ext_canonical,
  omega24Ext_ne,
  omega24Ext_fiber_inj,
  omega24Ext_pow_domain,
  pR_omega24Ext_eq,
  friSetupDeployedExt_C,
  friCodeDeployedExt_eq_extCode,
  deepCodeDeployedExt_eq_extCode,
  deepCodeDeployedExt_le_friCodeDeployedExt,
  deployedPtsExt_inj,
  deployedExt_closeN_decode
]

#assert_all_clean [
  extMatrix_col,
  colsClose_extMatrix_iff,
  deployed_colsClose_ext_iff,
  deployed_colsClose_ofWord_iff,
  colsClose_interpolants,
  deployed_deep_input_closeN,
  deployed_deep_input_closeN_of_colsClose,
  deployed_deep_input_coords_close,
  deployed_wire_radius_exceeds_ud
]

#assert_all_clean [
  exists_not_mem_range_algebraMap,
  extCode_beyond_base_image,
  fire_deployed_base_codeword_embeds,
  fire_deployed_ext_word_beyond_base,
  fire_deployed_backward_failure,
  fire_deployed_wire_hypotheses_inhabited,
  f4_finrank,
  fire_small_base_codeword_embeds,
  fire_small_ext_word_beyond_base,
  fire_small_relation,
  fire_small_backward_failure
]

end Dregg2.Circuit.FriDeployedExtCode
