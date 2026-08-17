/-
# Bfv.ZqSumcheck — sumcheck-over-Z_Q mathematics: the sampling-set Schwartz–Zippel,
# the provenance forgery UNSTATABLE, and the rescale UN-ARITHMETIZABLE.

**The lane.** `Bfv/CrossLimb.lean` exhibited the two cross-limb holes: HOLE A (provenance — the
`∀∃`/`∃∀` swap `perLimb_not_imp_bound`) and HOLE B (expressibility — `rescale_not_limb_local`).
This module is the algebraic route to the same wounds: run the sumcheck **natively over the
product ring** `Z_Q ≅ ∏ F_{qᵢ}` with challenges from a *sampling set* (CCKP19 / Bishnoi et al.:
pairwise differences invertible). Three findings, each a theorem here:

  * **The sampling-set Schwartz–Zippel** (`agree_card_lt_of_proj` + the product corollaries):
    distinct degree-<d polynomials over `∏ Kᵢ` agree on fewer than `d` points of any sampling
    set — proved by ONE coordinate projection reusing mathlib's field root counting, no new
    root counting. With its negative control `zq_fieldwide_sz_false`: **the field-wide statement
    is FALSE over a product ring** (distinct degree-<2 polynomials agreeing on 5 > 2 points), so
    the `[Field F]` binder in `Selvage/Sumcheck.lean`'s `card_agreeFinset_lt` is not cosmetically
    weakenable — the STATEMENT must move to a sampling set, and this file is that statement.
    The ceiling `samplingSet_card_le`: **no sampling set beats the smallest limb field** — at the
    deployed tower, `2³⁶` (`deployed_sampling_ceiling`), which is why amplification must be a
    ring extension, not a bigger set.
  * **HOLE A IS UNSTATABLE OVER Z_Q** (`boundMul_iff_zqBound` + `zq_same_forgery_refused`): the
    honest bound relation — one selector pair, EVERY limb — is *definitionally* one ring
    equation `out = pool ja * pool jb`, because the ring product does the per-limb conjunction
    with the selector already outside it. CrossLimb's frankenstein, the object that satisfies
    every per-limb equation (`exhibit_perLimb`), is over Z_Q a flatly FALSE statement: there is
    no per-limb slot left to satisfy. The forgery is not refused by an added check; the sentence
    it needs cannot be formed.
  * **HOLE B SURVIVES, now as a theorem** (`ringHom_eval_comm` → `rescale_not_zq_polynomial`):
    polynomials over a product ring compute EXACTLY the limb-local functions — coordinate `i` of
    `p.eval x` reads only coordinate `i` of `x`. The ct×ct rescale `⌊t·x/Q⌉` is not limb-local
    (`rescale_not_limb_local`), so **no polynomial over Z_Q computes it**, however the operands
    are bound. The satisfiable twin `mul_is_zq_polynomial` (the multiply itself IS `X·X`) keeps
    the refutation non-vacuous. The brief's hope that a Z_Q-native statement "CAN name the CRT
    reconstruction" is thereby HALF-refuted: nameable as a *function* (`crtRescale` is
    well-defined), never as a Z_Q-*polynomial* identity — the object a sumcheck natively checks.

**What this file does NOT do, said out loud.** No protocol theorem is proved here — the
round/union-bound machinery lives in `minidregg/Selvage` (`Sumcheck.lean`, whose probability
layer is already field-free and whose ONLY field-bound lemma is the one this file's sampling-set
counting replaces); the port map is `notes/zq-sumcheck.md` §3 in zkml-research. And as
everywhere in `Bfv/`, nothing here says any deployed Rust does any of this — there is no Z_Q
prover in the tree; these are the statements one would have to discharge.

Pure. No axioms beyond the kernel triple.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Field.ZMod
import Bfv.CrossLimb

namespace Bfv

open Polynomial Finset

/-! ## 1. Limb-locality: evaluation over a product ring is coordinate-wise.

The single most load-bearing fact in this file, used with OPPOSITE signs: for Hole A it is why
a Z_Q identity checked at one shared challenge pins every limb against the SAME selector (§3);
for Hole B it is why no Z_Q polynomial can compute a function that reads across limbs (§4). -/

/-- Evaluation commutes with any ring hom: `f (p.eval x) = (p.map f).eval (f x)`. -/
theorem ringHom_eval_comm {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : Polynomial R) (x : R) : f (p.eval x) = (p.map f).eval (f x) := by
  rw [← Polynomial.eval₂_hom, Polynomial.eval₂_eq_eval_map]

/-- **Limb-locality, first coordinate.** Over `R × S`, the first coordinate of a polynomial's
value is a function of the first coordinate of its input. -/
theorem eval_fst {R S : Type*} [CommSemiring R] [CommSemiring S]
    (p : Polynomial (R × S)) (x : R × S) :
    (p.eval x).1 = (p.map (RingHom.fst R S)).eval x.1 :=
  ringHom_eval_comm (RingHom.fst R S) p x

/-- Limb-locality, second coordinate. -/
theorem eval_snd {R S : Type*} [CommSemiring R] [CommSemiring S]
    (p : Polynomial (R × S)) (x : R × S) :
    (p.eval x).2 = (p.map (RingHom.snd R S)).eval x.2 :=
  ringHom_eval_comm (RingHom.snd R S) p x

/-- Limb-locality for an `L`-limb product: coordinate `i` of `p.eval x` reads only `x i`. -/
theorem eval_pi {L : ℕ} {K : Fin L → Type*} [∀ i, CommSemiring (K i)]
    (p : Polynomial (∀ i, K i)) (x : ∀ i, K i) (i : Fin L) :
    p.eval x i = (p.map (Pi.evalRingHom K i)).eval (x i) :=
  ringHom_eval_comm (Pi.evalRingHom K i) p x

/-- The congruence form: inputs agreeing at limb `i` produce outputs agreeing at limb `i` —
for EVERY polynomial over the product ring. This is the exact property
`rescale_not_limb_local` refutes for the rescale, which is the whole of §4. -/
theorem eval_pi_congr {L : ℕ} {K : Fin L → Type*} [∀ i, CommSemiring (K i)]
    (p : Polynomial (∀ i, K i)) {x y : ∀ i, K i} {i : Fin L} (h : x i = y i) :
    p.eval x i = p.eval y i := by
  rw [eval_pi, eval_pi, h]

/-! ## 2. The sampling-set Schwartz–Zippel, by coordinate projection.

CCKP19 Lemma 3 (citing Bishnoi–Clark–Potukuchi–Schmitt) for the ring we actually deploy: a
finite product of finite fields. The general non-zero-divisor form needs an iterated factor
theorem; for a product of fields ONE separating coordinate reuses mathlib's field root counting
verbatim — the engine below is coordinate-agnostic (`π` is any hom into a field), and the
product corollaries feed it the coordinate where the polynomials disagree. -/

/-- **The engine.** One ring hom `π` into a field that separates `p` from `q` and is injective
on `A` bounds the agreement inside `A` by the degree. Mathlib's `card_le_degree_of_subset_roots`
does the counting; `ringHom_eval_comm` moves the agreement into the field. -/
theorem agree_card_lt_of_proj {R F : Type*} [CommRing R] [DecidableEq R] [Field F]
    [DecidableEq F] (π : R →+* F) (A : Finset R) (hinj : Set.InjOn π ↑A)
    {d : ℕ} {p q : Polynomial R}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ))
    (hne : p.map π ≠ q.map π) :
    (A.filter fun x => p.eval x = q.eval x).card < d := by
  have hpj : (p.map π).degree < (d : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_map_le hp
  have hqj : (q.map π).degree < (d : WithBot ℕ) := lt_of_le_of_lt Polynomial.degree_map_le hq
  have hr0 : p.map π - q.map π ≠ 0 := sub_ne_zero.mpr hne
  have hrdeg : (p.map π - q.map π).degree < (d : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hpj hqj)
  have hrnat : (p.map π - q.map π).natDegree < d :=
    (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hrdeg
  have hsub : ((A.filter fun x => p.eval x = q.eval x).image π).val
      ⊆ (p.map π - q.map π).roots := by
    intro y hy
    rw [Finset.mem_val, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hagree := (Finset.mem_filter.mp hx).2
    have hfield : (p.map π).eval (π x) = (q.map π).eval (π x) := by
      rw [← ringHom_eval_comm, ← ringHom_eval_comm, hagree]
    rw [Polynomial.mem_roots hr0]
    simp [Polynomial.IsRoot, Polynomial.eval_sub, hfield]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injOn
    (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))] at hcard
  exact lt_of_le_of_lt hcard hrnat

/-- Distinct polynomials over `R × S` differ under at least one coordinate projection —
coefficients live in the product, so agreement under both projections is agreement. -/
theorem exists_prod_map_ne {R S : Type*} [CommSemiring R] [CommSemiring S]
    {p q : Polynomial (R × S)} (hne : p ≠ q) :
    p.map (RingHom.fst R S) ≠ q.map (RingHom.fst R S) ∨
      p.map (RingHom.snd R S) ≠ q.map (RingHom.snd R S) := by
  by_contra hc
  rw [not_or, not_ne_iff, not_ne_iff] at hc
  refine hne (Polynomial.ext fun n => ?_)
  have h1 := congrArg (fun r => r.coeff n) hc.1
  have h2 := congrArg (fun r => r.coeff n) hc.2
  simp only [Polynomial.coeff_map] at h1 h2
  exact Prod.ext h1 h2

/-- **Sampling-set Schwartz–Zippel over a product of two fields** — the deployed shape at
`L = 2`, and the induction step for any nesting. The sampling condition is stated in its
product-of-fields normal form: distinct elements of `A` differ in EVERY limb (equivalent to
`IsUnit (a − b)`, `samplingSet_isUnit_iff` below — CCKP19's non-zero-divisor condition, which
in a finite ring is the same thing). -/
theorem zq_agree_card_lt {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S]
    (A : Finset (R × S))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.1 ≠ b.1 ∧ a.2 ≠ b.2)
    {d : ℕ} {p q : Polynomial (R × S)}
    (hp : p.degree < (d : WithBot ℕ)) (hq : q.degree < (d : WithBot ℕ)) (hne : p ≠ q) :
    (A.filter fun x => p.eval x = q.eval x).card < d := by
  rcases exists_prod_map_ne hne with h | h
  · refine agree_card_lt_of_proj (RingHom.fst R S) A ?_ hp hq h
    intro x hx y hy hxy
    by_contra hne'
    exact (hA x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne').1 hxy
  · refine agree_card_lt_of_proj (RingHom.snd R S) A ?_ hp hq h
    intro x hx y hy hxy
    by_contra hne'
    exact (hA x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne').2 hxy

/-- The sampling condition IS invertible differences (CCKP19's condition, in the form their
Remark 1 asks for): over a product of fields, `IsUnit (a − b)` ⟺ the elements differ in every
limb. -/
theorem samplingSet_isUnit_iff {L : ℕ} {K : Fin L → Type*} [∀ i, Field (K i)]
    (a b : ∀ i, K i) : IsUnit (a - b) ↔ ∀ i, a i ≠ b i := by
  rw [Pi.isUnit_iff]
  exact forall_congr' fun i => by rw [Pi.sub_apply, isUnit_iff_ne_zero, sub_ne_zero]

/-- ⚑ **THE NEGATIVE CONTROL — field-wide Schwartz–Zippel is FALSE over a product ring.**
`p = C (1,0) · X` and `q = 0` are distinct, both of degree `< 2`, and agree on the entire
`{0} × F₅` fiber: 5 > 2 points. This is why `Selvage/Sumcheck.lean`'s `card_agreeFinset_lt`
cannot be generalized by weakening its `[Field F]` binder: the STATEMENT is wrong over `Z_Q`,
and the sampling-set restriction of `zq_agree_card_lt` is load-bearing, not decorative. -/
theorem zq_fieldwide_sz_false :
    ∃ p q : Polynomial (ZMod 3 × ZMod 5), p ≠ q ∧
      p.degree < ((2 : ℕ) : WithBot ℕ) ∧ q.degree < ((2 : ℕ) : WithBot ℕ) ∧
      2 < (Finset.univ.filter fun x : ZMod 3 × ZMod 5 => p.eval x = q.eval x).card := by
  refine ⟨Polynomial.C ((1 : ZMod 3), (0 : ZMod 5)) * Polynomial.X, 0, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun r => Polynomial.coeff r 1) h
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
      Polynomial.coeff_zero] at h1
    exact absurd h1 (by decide)
  · exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by decide)
  · rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  · have hsub : (Finset.univ.image fun y : ZMod 5 => ((0 : ZMod 3), y))
        ⊆ Finset.univ.filter fun x : ZMod 3 × ZMod 5 =>
            (Polynomial.C ((1 : ZMod 3), (0 : ZMod 5)) * Polynomial.X).eval x
              = (0 : Polynomial (ZMod 3 × ZMod 5)).eval x := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [Prod.mk_mul_mk]
    have hcard : (Finset.univ.image fun y : ZMod 5 => ((0 : ZMod 3), y)).card = 5 := by
      rw [Finset.card_image_of_injective _ fun a b h => congrArg Prod.snd h,
        Finset.card_univ, ZMod.card]
    have hle := Finset.card_le_card hsub
    omega

/-! ### The ceiling: no sampling set beats the smallest limb field. -/

/-- Any injective-on-`A` coordinate bounds `A` by its codomain — the reason a sampling set of a
product ring can never exceed the SMALLEST factor: a shared coordinate makes the difference a
zero divisor, so every coordinate is injective on `A`. -/
theorem samplingSet_card_le {R T : Type*} [DecidableEq T] [Fintype T]
    (A : Finset R) (f : R → T) (hf : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → f a ≠ f b) :
    A.card ≤ Fintype.card T := by
  have hinj : Set.InjOn f ↑A := by
    intro x hx y hy hxy
    by_contra hne
    exact hf x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne hxy
  calc A.card = (A.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset T).card := Finset.card_le_univ _
    _ = Fintype.card T := Finset.card_univ

/-- ⚑ **The deployed ceiling is `q₁ = 0xffffc4001 ≈ 2³⁶.** Any sampling set of the deployed
tower `F_{q₀} × F_{q₁} × F_{q₂}` has at most `q₁` elements — the base-ring soundness of a
Z_Q sumcheck is capped at ~36 bits per `d`, and only a ring EXTENSION (one `f` simultaneously
irreducible mod each prime, `notes/zq-sumcheck.md` §2) raises it. The other 73 bits of `Q` are
unrecoverable by a better set: this is a theorem, not a design choice. -/
theorem deployed_sampling_ceiling
    (A : Finset (ZMod 0xffffee001 × ZMod 0xffffc4001 × ZMod 0x1ffffe0001))
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      a.1 ≠ b.1 ∧ a.2.1 ≠ b.2.1 ∧ a.2.2 ≠ b.2.2) :
    A.card ≤ 0xffffc4001 := by
  haveI : NeZero (0xffffc4001 : ℕ) := ⟨by norm_num⟩
  have h := samplingSet_card_le A (fun x => x.2.1)
    (fun a ha b hb hne => (hA a ha b hb hne).2.1)
  rwa [ZMod.card] at h

instance : Fact (Nat.Prime 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The ceiling is ATTAINED (satisfiability, exhibit scale): the diagonal
`{(0,0),(1,1),(2,2)} ⊆ F₃ × F₅` is a genuine sampling set of card `3 = |F₃| = min`. -/
def zqSamplingA : Finset (ZMod 3 × ZMod 5) :=
  {((0 : ZMod 3), (0 : ZMod 5)), (1, 1), (2, 2)}

theorem zqSamplingA_sound :
    ∀ a ∈ zqSamplingA, ∀ b ∈ zqSamplingA, a ≠ b → a.1 ≠ b.1 ∧ a.2 ≠ b.2 := by decide

theorem zqSamplingA_attains_ceiling :
    zqSamplingA.card = 3 ∧ Fintype.card (ZMod 3) = 3 := by decide

/-- **The sampling-set bound FIRES on data** (teeth: nonempty agreement, bound respected):
`p = X` and `q = 0` agree inside `zqSamplingA` only at `(0,0)` — a nonempty set, of card `< 2`
exactly as `zq_agree_card_lt` demands. -/
theorem zq_sz_fires :
    ((0 : ZMod 3), (0 : ZMod 5)) ∈
        (zqSamplingA.filter fun x => (Polynomial.X : Polynomial (ZMod 3 × ZMod 5)).eval x
          = (0 : Polynomial (ZMod 3 × ZMod 5)).eval x) ∧
      (zqSamplingA.filter fun x => (Polynomial.X : Polynomial (ZMod 3 × ZMod 5)).eval x
          = (0 : Polynomial (ZMod 3 × ZMod 5)).eval x).card < 2 := by
  constructor
  · simp only [Finset.mem_filter, Polynomial.eval_X, Polynomial.eval_zero]
    exact ⟨Finset.mem_insert_self _ _, by decide⟩
  · have hdX : (Polynomial.X : Polynomial (ZMod 3 × ZMod 5)).degree < ((2 : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt Polynomial.degree_X_le (by decide)
    have hd0 : (0 : Polynomial (ZMod 3 × ZMod 5)).degree < ((2 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    have hne : (Polynomial.X : Polynomial (ZMod 3 × ZMod 5)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun r => Polynomial.coeff r 1) h
      simp only [Polynomial.coeff_X_one, Polynomial.coeff_zero] at h1
      exact absurd h1 (by decide)
    exact zq_agree_card_lt zqSamplingA zqSamplingA_sound hdX hd0 hne

#assert_all_clean [Bfv.ringHom_eval_comm, Bfv.eval_fst, Bfv.eval_snd, Bfv.eval_pi,
  Bfv.eval_pi_congr, Bfv.agree_card_lt_of_proj, Bfv.exists_prod_map_ne, Bfv.zq_agree_card_lt,
  Bfv.samplingSet_isUnit_iff, Bfv.zq_fieldwide_sz_false, Bfv.samplingSet_card_le,
  Bfv.deployed_sampling_ceiling, Bfv.zqSamplingA_sound, Bfv.zqSamplingA_attains_ceiling,
  Bfv.zq_sz_fires]

/-! ## 3. HOLE A UNSTATABLE: the Z_Q relation IS the bound relation.

`CrossLimb` separates `BoundMul` (∃ pair, ∀ limb — honest) from `PerLimbMul` (∀ limb, ∃ pair —
what a per-limb verifier buys) and exhibits their gap. Over the ring the gap cannot be WRITTEN:
a relation about Z_Q pool elements has ONE selector pair and ONE ring equation, and the ring
equation does the per-limb conjunction itself — the selector is outside the coordinate split by
the syntax of the ring, not by a checked constraint. -/

/-- A ciphertext coefficient as ONE ring element of `F₃ × F₅` — the CRT view of the exhibit's
two limbs (`exhibitQ = (3,5)`, `N = 1`). Compare `RnsCt`, which stores the limbs as independent
residue vectors: `zqOf` is the forgetful map from the attack-representable carrier into the ring
where the attack loses its slots. -/
def zqOf (c : RnsCt 2 1) : ZMod 3 × ZMod 5 := (((c 0 0 : ℤ) : ZMod 3), ((c 1 0 : ℤ) : ZMod 5))

/-- **The Z_Q-native multiplication relation**: one selector pair, one ring equation. This is
the ENTIRE statement a Z_Q sumcheck instance makes about provenance — there is no per-limb
version of it to weaken. -/
def ZqBoundMul {R : Type*} [Mul R] {K : ℕ} (pool : Fin K → R) (out : R) : Prop :=
  ∃ ja jb : Fin K, out = pool ja * pool jb

/-- One limb's integer congruence at `N = 1` is one `ZMod` coordinate equation. -/
theorem limbMulRel_one_iff_zmod (q : ℕ) (a b c : Rn 1) :
    LimbMulRel q a b c ↔ ((c 0 : ℤ) : ZMod q) = ((a 0 : ℤ) : ZMod q) * ((b 0 : ℤ) : ZMod q) := by
  rw [limbMulRel_iff_modEq]
  constructor
  · intro h
    have h0 := h 0
    rw [negaMul_one_eq_mul] at h0
    calc ((c 0 : ℤ) : ZMod q) = ((a 0 * b 0 : ℤ) : ZMod q) :=
          (ZMod.intCast_eq_intCast_iff _ _ _).mpr h0
      _ = _ := by push_cast; ring
  · intro h k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst hk
    rw [negaMul_one_eq_mul]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (by push_cast; exact h)

/-- ⚑ **UNSTATABILITY, the positive half: the honest relation IS the ring equation.** For any
pool and output, CrossLimb's `BoundMul` at the exhibit basis holds **iff** the single Z_Q
statement `∃ ja jb, zqOf out = zqOf (pool ja) * zqOf (pool jb)` holds. The `∃∀` shape is not a
design choice a Z_Q verifier makes; it is what a ring equation *means*. (The algebraic twin of
`boundMul_iff_sharedSelector`, with the ring product doing the limb conjunction.) -/
theorem boundMul_iff_zqBound {K : ℕ} (pool : Fin K → RnsCt 2 1) (out : RnsCt 2 1) :
    BoundMul exhibitQ pool out ↔ ZqBoundMul (fun j => zqOf (pool j)) (zqOf out) := by
  unfold BoundMul ZqBoundMul
  refine exists₂_congr fun ja jb => ?_
  rw [Fin.forall_fin_two,
    show exhibitQ 0 = 3 from rfl, show exhibitQ 1 = 5 from rfl,
    limbMulRel_one_iff_zmod, limbMulRel_one_iff_zmod]
  simp [zqOf, Prod.ext_iff]

/-- ⚑ **UNSTATABILITY, the teeth: the SAME forgery, refused as a false sentence.** CrossLimb's
frankenstein satisfies every per-limb equation (`exhibit_perLimb`, cited not re-proved) — and
over Z_Q it is simply FALSE: no pair from the pool multiplies to it. A per-limb verifier
accepts it; a Z_Q verifier is never even ASKED about it, because the per-limb statement it
satisfies does not exist over the ring. Soundness of the Z_Q sumcheck (`zq_agree_card_lt` per
round) then catches the false claim except with `v·d/|A|`. -/
theorem zq_same_forgery_refused :
    PerLimbMul exhibitQ exhibitPool exhibitOut ∧
      ¬ ZqBoundMul (fun j => zqOf (exhibitPool j)) (zqOf exhibitOut) :=
  ⟨exhibit_perLimb, fun h => exhibit_not_bound ((boundMul_iff_zqBound exhibitPool exhibitOut).mpr h)⟩

/-- Satisfiability (house law): the honest product DOES satisfy the ring statement — inherited
from `exhibit_bound_satisfiable` through the iff, so the refuted predicate is non-vacuous. -/
theorem zqBound_satisfiable :
    ZqBoundMul (fun j => zqOf (exhibitPool j))
      (zqOf fun i => negaMul (exhibitPool 0 i) (exhibitPool 0 i)) :=
  (boundMul_iff_zqBound exhibitPool _).mp exhibit_bound_satisfiable

#assert_all_clean [Bfv.limbMulRel_one_iff_zmod, Bfv.boundMul_iff_zqBound,
  Bfv.zq_same_forgery_refused, Bfv.zqBound_satisfiable]

/-! ## 4. HOLE B SURVIVES: the rescale is not a Z_Q polynomial.

The brief's expressibility hope, checked. Over the ring the rescale `⌊t·x/Q⌉` IS a well-defined
function of the ring element (`crtRescale` below — that half of the hope is TRUE, and is exactly
what per-limb representations lack, `rescale_not_limb_local`). But a Z_Q-native SUMCHECK checks
Z_Q-*polynomial* identities, and §1's limb-locality says polynomials compute only limb-local
functions — so the rescale is out of reach of any polynomial arithmetization over Z_Q, and its
fix stays what it was: witness structure carrying the reconstruction (redundant basis or a
single prime). CCKP19 corroborate from the other side: they work over `Z_{p^e}` — NOT a CRT
product — precisely so that base-p rounding is low-degree-polynomial (their §V). -/

/-- CRT lift to the canonical representative in `[0, 15)` — `exhibitCrt`'s reconstruction, as a
function of the ring element (`10 ≡ (1,0)`, `6 ≡ (0,1)`). -/
def lift15 (x : ZMod 3 × ZMod 5) : ℤ := (10 * (x.1.val : ℤ) + 6 * (x.2.val : ℤ)) % 15

/-- The ct×ct rescale `⌊t·x/Q⌉` at the exhibit parameters `t = 2, Q = 15`, as a FUNCTION of the
ring element — well-defined, which no single limb can offer. Nameable: yes. Polynomial: no
(`rescale_not_zq_polynomial`). -/
def crtRescale (x : ZMod 3 × ZMod 5) : ZMod 3 × ZMod 5 :=
  ((rescale 2 15 (lift15 x) : ℤ), (rescale 2 15 (lift15 x) : ℤ))

/-- The computed values the refutation rides (also the decidability canary): `0` and `6` in
`ℤ/15` share the limb-3 residue `0`, and their rescales `0` and `1` do not. -/
theorem crtRescale_computed :
    crtRescale ((0 : ZMod 3), (0 : ZMod 5)) = (0, 0) ∧
      crtRescale ((0 : ZMod 3), (1 : ZMod 5)) = (1, 1) := by decide

/-- ⚑ **HOLE B OVER Z_Q, EXHIBITED AS AN IMPOSSIBILITY.** No polynomial over the product ring
computes the rescale: the inputs `(0,0)` and `(0,1)` agree in the first limb, every
polynomial's output must too (`eval_fst`), and the rescale's outputs differ there
(`crtRescale_computed`). Binding the operands — Hole A's closure, §3 — does not touch this;
the two holes are independent over Z_Q exactly as they were per-limb. -/
theorem rescale_not_zq_polynomial :
    ¬ ∃ p : Polynomial (ZMod 3 × ZMod 5), ∀ x, p.eval x = crtRescale x := by
  rintro ⟨p, hp⟩
  have hloc : (p.eval ((0 : ZMod 3), (0 : ZMod 5))).1
      = (p.eval ((0 : ZMod 3), (1 : ZMod 5))).1 := by
    rw [eval_fst, eval_fst]
  rw [hp, hp] at hloc
  rw [crtRescale_computed.1, crtRescale_computed.2] at hloc
  exact absurd hloc (by decide)

/-- The satisfiable twin (house law): the ct×ct MULTIPLY is a Z_Q polynomial — `X·X` computes
squaring — so §1's locality does not refute arithmetization wholesale. The multiply is
Z_Q-native; the rescale alone is not. -/
theorem mul_is_zq_polynomial :
    ∃ p : Polynomial (ZMod 3 × ZMod 5), ∀ x, p.eval x = x * x :=
  ⟨Polynomial.X * Polynomial.X, fun x => by simp⟩

#assert_all_clean [Bfv.crtRescale_computed, Bfv.rescale_not_zq_polynomial,
  Bfv.mul_is_zq_polynomial]

end Bfv
