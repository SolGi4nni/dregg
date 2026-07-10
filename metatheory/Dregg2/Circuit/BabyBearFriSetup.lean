import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.BabyBearFriField

/-!
# DEBT-A brick 2 — a genuine FRI `FriSetup` over the DEPLOYED BabyBear field

**Honest scope (first sentence).** This file constructs a genuine Reed-Solomon `FriGeom`/`FriSetup`
over `BabyBear` (`ZMod 2013265921`, the DEPLOYED prover field of brick 1) on a **domain of size
`2^k = 4`** — the order-`4` multiplicative subgroup `L = {1, i, -1, -i}` of `BabyBear*` (`i` = a
concrete primitive fourth root of unity, `i² = -1`) — and **INSTANTIATES** the field-generic PROVED
lemmas `friProximity_discharge` and `fold_close_of_two_alpha` at it (`babyBear_friProximity_discharge`,
`babyBear_fold_close` are those lemmas *applied*, no new hypothesis re-assumed). It proves the geometry
meets the FRI axioms, the RS-closure facts, and BOTH tooth polarities at BabyBear. It does **NOT** bind
to the deployed p3 FRI **domain size / rate / query count** — matching a `2^27`-sized evaluation domain,
the concrete blow-up rate, and the sampled-query soundness parameter of the shipped `verifyBatch` config
is **brick 3**. This brick proves the FRI geometry instantiates at the deployed **FIELD**; a small
`2^k = 4` domain is a *faithful instance of the same construction* (real coset, real squaring quotient —
`pVal_sq_eq` witnesses `q` IS squaring), not the deployed domain size. A subset labeled complete is a
lie: `|L| = 4 ≠ 2^27`.

Mirrors the `ZMod 5` demo of `FriSoundness.lean` (`§5`, `rsGeom`/`rsSetup`) exactly, swapping the field
`ZMod 5 → BabyBear`. The `ZMod 5` domain was the order-`4` group `{1,2,3,4}`; here it is the order-`4`
group `{1, i, -1, -i}` of the deployed field — same size, same construction, deployed field.
-/

namespace Dregg2.Circuit.BabyBearFriSetup

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-! ## The order-`4` multiplicative subgroup `L = {1, i, -1, -i}` of `BabyBear*`.

`i = 1728404513` is a concrete primitive fourth root of unity: `i² = -1` (`iVal_sq`, checked by the
kernel — a `ZMod 2013265921` numeral computation). So `L` is a REAL power-of-two multiplicative coset
of the deployed field, closed under negation, on which squaring is exactly `2`-to-`1`. (The data defs
are `noncomputable` only because BabyBear's `Field` instance is; the kernel still decides the numeral
facts below — `decide` uses kernel reduction, not compiled code.) -/

/-- A concrete primitive fourth root of unity in BabyBear (`i² = -1`). -/
noncomputable def iVal : BabyBear := 1728404513

/-- **`i² = -1`** — `i` is a genuine order-`4` element (the kernel verifies the `ZMod` numeral). -/
theorem iVal_sq : iVal * iVal = -1 := by decide

/-- `i ≠ 0`. -/
theorem iVal_ne_zero : iVal ≠ 0 := by decide

/-- `L = {1, i, -1, -i} ⊂ BabyBear`, indexed by `Fin 4` (the order-`4` subgroup). -/
noncomputable def pVal : Fin 4 → BabyBear := ![1, iVal, -1, -iVal]
/-- Squaring `L → L²`: `1²=1, i²=-1, (-1)²=1, (-i)²=-1` ↦ `{κ₀ = 1, κ₁ = -1}`. -/
def qMap : Fin 4 → Fin 2 := ![0, 1, 0, 1]
/-- Negation `x ↦ -x`: `1↔-1` (`0↔2`), `i↔-i` (`1↔3`). -/
def sigMap : Fin 4 → Fin 4 := ![2, 3, 0, 1]
/-- Section of `q`: `κ₀ ↦ 1` (idx 0), `κ₁ ↦ i` (idx 1). -/
def repMap : Fin 2 → Fin 4 := ![0, 1]
/-- `L² = {1, -1}` indexed by `Fin 2` — used only to WITNESS that `q` is genuine squaring. -/
noncomputable def l2Val : Fin 2 → BabyBear := ![1, -1]

/-- **Faithfulness: `q` IS squaring.** For every `x ∈ L`, `(pVal x)² = l2Val (qMap x)` — the index
map `qMap` reflects the REAL field squaring of the coset onto `L² = {1,-1}` (needs `i² = -1`). This is
what makes the setup a genuine RS instance, not a shell. -/
theorem pVal_sq_eq (x : Fin 4) : (pVal x) ^ 2 = l2Val (qMap x) := by
  fin_cases x <;> decide

/-- The concrete coset geometry over BabyBear — every FRI axiom holds. The index axioms
(`q_rep`/`q_σ_rep`/`q_fiber`) are pure `Fin` facts; the value axioms (`two_ne`/`p_rep_ne`/`p_σ_rep`)
are `ZMod 2013265921` numeral checks — all by the kernel decision procedure, mirroring the `ZMod 5`
demo's `rsGeom`. -/
noncomputable def babyBearFriGeom : FriGeom BabyBear (Fin 4) (Fin 2) where
  σ := sigMap
  q := qMap
  p := pVal
  rep := repMap
  two_ne := by decide
  q_rep := by decide
  q_σ_rep := by decide
  p_rep_ne := by decide
  p_σ_rep := by decide
  q_fiber := by decide

/-! ## The Reed-Solomon codes over BabyBear.

`C = {x ↦ a + b·pVal x}` (evaluations of deg `< 2` polys, rate `1/2`); `C' = {constants}` (deg `< 1`).
Identical to the `ZMod 5` `rsC`/`rsC'`, over the deployed field. -/

/-- The domain code `C = {x ↦ a + b·pVal x}` — deg `< 2` evaluations. -/
noncomputable def bbC : Submodule BabyBear (Fin 4 → BabyBear) where
  carrier := {f | ∃ a b : BabyBear, f = fun x => a + b * pVal x}
  zero_mem' := ⟨0, 0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by funext x; simp; ring⟩
  smul_mem' := by
    rintro c f ⟨a, b, rfl⟩
    exact ⟨c * a, c * b, by funext x; simp [mul_add]; ring⟩

/-- The folded code `C' = {constants}` — deg `< 1`. -/
noncomputable def bbC' : Submodule BabyBear (Fin 2 → BabyBear) where
  carrier := {g | ∃ a : BabyBear, g = fun _ => a}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro f g ⟨a, rfl⟩ ⟨a', rfl⟩; exact ⟨a + a', rfl⟩
  smul_mem' := by rintro c f ⟨a, rfl⟩; exact ⟨c * a, rfl⟩

theorem mem_bbC {f} : f ∈ bbC ↔ ∃ a b : BabyBear, f = fun x => a + b * pVal x := Iff.rfl
theorem mem_bbC' {g} : g ∈ bbC' ↔ ∃ a : BabyBear, g = fun _ => a := Iff.rfl

/-- **The genuine Reed-Solomon FRI setup over BabyBear** — closure facts PROVED, mirroring the
`ZMod 5` `rsSetup`. -/
noncomputable def babyBearFriSetup : FriSetup BabyBear (Fin 4) (Fin 2) where
  geom := babyBearFriGeom
  C := bbC
  C' := bbC'
  unfold_closed := by
    rintro Ge ⟨ce, rfl⟩ Go ⟨co, rfl⟩
    exact ⟨ce, co, by funext x; simp only [unfoldF, babyBearFriGeom]; ring⟩
  foldE_mem := by
    rintro f ⟨a, b, rfl⟩
    refine ⟨a, ?_⟩
    funext y
    have hps : pVal (sigMap (repMap y)) = - pVal (repMap y) := by fin_cases y <;> decide
    simp only [E, babyBearFriGeom]
    rw [hps]
    rw [div_eq_iff (show (2 : BabyBear) ≠ 0 by decide)]
    ring
  foldO_mem := by
    rintro f ⟨a, b, rfl⟩
    refine ⟨b, ?_⟩
    funext y
    have hps : pVal (sigMap (repMap y)) = - pVal (repMap y) := by fin_cases y <;> decide
    have hpne : (2 : BabyBear) * pVal (repMap y) ≠ 0 := by fin_cases y <;> decide
    simp only [O, babyBearFriGeom]
    rw [hps]
    rw [div_eq_iff hpne]
    ring

/-! ## §Payoff — the field-generic PROVED lemmas, INSTANTIATED at the deployed field.

These are `friProximity_discharge` and `fold_close_of_two_alpha` (`FriSoundness.lean`, `[Field F]
[DecidableEq F]`-generic, no `sorry`) *applied* at `babyBearFriSetup` — no new hypothesis re-assumed. The
"field-swap the census flagged as missing" is exactly this application. -/

/-- An honest low-degree codeword `f = 2 + 3·pVal` over BabyBear. -/
noncomputable def fHonest : Fin 4 → BabyBear := fun x => 2 + 3 * pVal x

theorem fHonest_mem : fHonest ∈ babyBearFriSetup.C := ⟨2, 3, rfl⟩

/-- **`babyBear_friProximity_discharge` — `friProximity_discharge` INSTANTIATED at BabyBear.**
An accepting FRI transcript (query set `univ` covering the empty disagreement, all checks passing, a
final codeword, and a non-bad challenge whose fold-into-`C'` forces membership) discharges
`FriProximity` at the deployed field: the oracle is `0`-close, i.e. a genuine codeword. This is the
FIELD-GENERIC lemma APPLIED — every argument supplied, none re-assumed. -/
theorem babyBear_friProximity_discharge :
    FriProximity babyBearFriSetup 0 fHonest :=
  friProximity_discharge babyBearFriSetup (f := fHonest) (α := 0)
    (f' := Fold babyBearFriSetup.geom 0 fHonest) Finset.univ
    (Finset.subset_univ _)
    (fun _ _ => rfl)
    (fold_complete babyBearFriSetup fHonest_mem 0)
    (fun _ => fHonest_mem)

/-- **`babyBear_fold_close` — `fold_close_of_two_alpha` INSTANTIATED at BabyBear.** Two DISTINCT
challenges (`0 ≠ 1`) both fold the honest codeword `0`-close to `C'` (completeness), so the KEY LEMMA
reconstructs it `4·0`-close to `C` at the deployed field. The field-generic distance-preservation
lemma, APPLIED. -/
theorem babyBear_fold_close :
    closeN babyBearFriSetup.C (4 * 0) fHonest :=
  fold_close_of_two_alpha babyBearFriSetup (f := fHonest) (α₁ := 0) (α₂ := 1)
    (by decide)
    (closeN_zero_iff_mem.mpr (fold_complete babyBearFriSetup fHonest_mem 0))
    (closeN_zero_iff_mem.mpr (fold_complete babyBearFriSetup fHonest_mem 1))

/-! ## §Teeth — both polarities at BabyBear (mirroring the `ZMod 5` `§5` witnesses). -/

/-- **Tooth 1 (close FIRES).** The honest codeword is `0`-close (exactly a codeword). -/
theorem fHonest_close0 : closeN babyBearFriSetup.C 0 fHonest :=
  closeN_zero_iff_mem.mpr fHonest_mem

/-- Its fold with ANY challenge lands in the folded code (completeness). -/
theorem fHonest_fold_mem (α : BabyBear) : Fold babyBearFriGeom α fHonest ∈ babyBearFriSetup.C' :=
  fold_complete babyBearFriSetup fHonest_mem α

/-- A FAR word `f = ![1,0,0,0]` (the point-`0` indicator) — NOT a codeword. -/
noncomputable def fFar : Fin 4 → BabyBear := ![1, 0, 0, 0]

/-- **`fFar ∉ C`** — proved by algebra (the domain is too large for `decide`): if `fFar = a + b·pVal`
then the sibling equations `h1 + h3` give `2a = 0` ⇒ `a = 0` (`2 ≠ 0`); then `h2` gives `b = 0`; so
`1 = a + b = 0`, absurd. Only needs `2 ≠ 0`, `1 ≠ 0` — no `i`-specific fact. -/
theorem fFar_not_mem : fFar ∉ babyBearFriSetup.C := by
  rw [show babyBearFriSetup.C = bbC from rfl, mem_bbC]
  rintro ⟨a, b, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [fFar, pVal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.isValue] at h0 h1 h2 h3
  -- h0: 1 = a + b*1 ; h1: 0 = a + b*i ; h2: 0 = a + b*(-1) ; h3: 0 = a + b*(-i)
  have ha : a = 0 := by
    have hsum : (2 : BabyBear) * a = 0 := by linear_combination -h1 - h3
    exact (mul_eq_zero.mp hsum).resolve_left (by decide)
  have hb : b = 0 := by
    rw [ha] at h2
    linear_combination h2
  rw [ha, hb] at h0
  simp only [mul_one, add_zero] at h0
  exact one_ne_zero h0

/-- **Tooth 2a (the collapsing challenge — close FIRES for exactly one `α`).** At `α = -1` the fold of
the far word collapses to the constant `0`, so it lands in `C'`. -/
theorem fFar_good_alpha : Fold babyBearFriGeom (-1) fFar ∈ babyBearFriSetup.C' := by
  rw [show babyBearFriSetup.C' = bbC' from rfl, mem_bbC']
  refine ⟨0, ?_⟩
  funext y
  fin_cases y <;> simp [Fold, E, O, babyBearFriGeom, sigMap, repMap, pVal, fFar]

/-- **Tooth 2b (a different challenge LEAVES the code — the KEY LEMMA bites).** At `α = 0` the fold is
non-constant: `Fold 0 fFar 0 = 2⁻¹ ≠ 0 = Fold 0 fFar 1`, so it is NOT in `C'`. -/
theorem fFar_bad_alpha : Fold babyBearFriGeom 0 fFar ∉ babyBearFriSetup.C' := by
  rw [show babyBearFriSetup.C' = bbC' from rfl, mem_bbC']
  rintro ⟨a, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have e0 : Fold babyBearFriGeom 0 fFar 0 = 2⁻¹ := by
    simp [Fold, E, O, babyBearFriGeom, sigMap, repMap, pVal, fFar]
  have e1 : Fold babyBearFriGeom 0 fFar 1 = 0 := by
    simp [Fold, E, O, babyBearFriGeom, sigMap, repMap, pVal, fFar]
  rw [e0] at h0
  rw [e1] at h1
  have hcontra : (2 : BabyBear)⁻¹ = 0 := h0.trans h1.symm
  exact (show (2 : BabyBear) ≠ 0 by decide) (inv_eq_zero.mp hcontra)

/-- **The KEY LEMMA fires on concrete BabyBear data**: the exceptional set of `fFar` is a subsingleton
(`exceptional_subsingleton` instantiated at `babyBearFriSetup`), with `α = -1` in it (`fFar_good_alpha`) and
`α = 0` not (`fFar_bad_alpha`) — EXACTLY ONE good challenge, witnessed at the deployed field. -/
theorem fFar_exceptional_subsingleton :
    {β : BabyBear | Fold babyBearFriGeom β fFar ∈ babyBearFriSetup.C'}.Subsingleton :=
  exceptional_subsingleton babyBearFriSetup fFar_not_mem

/-! ## §Axiom hygiene — the payoff theorems rest only on the kernel axioms (no `sorry`, no `def …Hard`,
no smuggled hardness; the `friProximity_discharge`/`fold_close_of_two_alpha` content is imported PROVED
and merely instantiated). -/

#assert_axioms babyBear_friProximity_discharge
#assert_axioms babyBear_fold_close
#assert_axioms fFar_exceptional_subsingleton
#assert_axioms pVal_sq_eq

end Dregg2.Circuit.BabyBearFriSetup
