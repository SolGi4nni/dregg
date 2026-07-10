import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.BabyBearFriField

/-!
# DEBT-A brick 3 — the BabyBear `FriSetup` PARAMETERIZED over the size-`2^(m+1)` domain,
instantiated at the DEPLOYED RATE and at the full 2-adicity cap.

**Honest scope (first sentence).** The shipped p3 FRI evaluation-domain **size is NOT a
static constant** — it is `padded_trace_height × 2^log_blowup`, fixed at prove time by the
AIR trace height, and only *bounded above* by BabyBear's 2-adicity `2^27` (`circuit/src/
plonky3_prover.rs:154` builds `FriParameters` from a runtime `degree`; brick 1's
`babyBear_two_adicity_lt_28` is the cap). What IS statically deployed is the **rate**
(`log_blowup = 3` ⇒ `1/8`, `plonky3_prover.rs:96`), `num_queries = 38`
(`:99`), `query_pow_bits = 16` (`:100`), `max_log_arity = 3` (`:98`),
`log_final_poly_len = 0` (`:97`). This file therefore (1) GENERALIZES brick 2's hard-coded
`Fin 4` geometry to a `Fin (2^(m+1))` domain (`σ` = negation, `q` = squaring, `rep` a
section) with proofs **general in `m`** — the geometry axioms are Nat/Fin modular arithmetic
plus TWO field facts (`ω ≠ 0`, `ω ^ (2^m) = -1`), NO per-point `decide`; (2) instantiates at
`m = 3` (`|L| = 2^4 = 16`, `|L²| = 8`) — the smallest domain whose degree-`2` Reed-Solomon
code has **exactly the DEPLOYED rate `1/8`** — with a concrete primitive `16`-th root
`ω₁₆` proved by `decide`; and (3) instantiates the SAME construction at `m = 26`
(`|L| = 2^27`, the 2-adicity cap) with a primitive `2^27`-th root `ω₂₇` proved by a
26-step iterated-squaring chain (each step one BabyBear numeral squaring by `decide`).
At `2^27` the degree-`2` code has rate `2^-26`, NOT the deployed `1/8`; matching the
deployed rate AND a large absolute domain needs a degree-`2^(m-2)` code whose folding
closure is a separate (unwritten) proof — FLAGGED below, not claimed. The payoff lemmas
`friProximity_discharge` / `fold_close_of_two_alpha` are the field-generic PROVED theorems
of `FriSoundness.lean` **APPLIED** at these setups (no new hypothesis). `|L| = 16 ≠` the
runtime deployed size; `|L| = 2^27` is the CAP, not any single shipped proof's domain.

Mirrors brick 2 (`BabyBearFriSetup.lean`) exactly; the only new content is the
`m`-parameterization and the two instantiations.
-/

namespace Dregg2.Circuit.BabyBearFriDeployed

open Dregg2.Circuit.FriSoundness
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-! ## §1. The parameterized size-`2^(m+1)` coset geometry.

`L = {ω^0, …, ω^(2^(m+1)-1)}` for a primitive `2^(m+1)`-th root of unity `ω`; indexed by
`Fin (2^(m+1))`. Squaring `q` sends `ω^j ↦ (ω^j)² = ω^(2j)`, whose fiber `{j, j+2^m}`
collapses to `j mod 2^m` in `L² = ⟨ω²⟩` (`Fin (2^m)`). Negation `σ` is `j ↦ (j+2^m) mod
2^(m+1)` (since `ω^(2^m) = -1`). `rep` embeds `Fin (2^m) ↪ Fin (2^(m+1))`. -/

/-- The point value `p(j) = ω^j`. -/
noncomputable def pParam (m : ℕ) (ω : BabyBear) : Fin (2 ^ (m + 1)) → BabyBear :=
  fun j => ω ^ (j : ℕ)

/-- The squaring quotient `q(j) = j mod 2^m : Fin (2^m)`. -/
def qParam (m : ℕ) : Fin (2 ^ (m + 1)) → Fin (2 ^ m) :=
  fun j => ⟨(j : ℕ) % 2 ^ m, Nat.mod_lt _ (pow_pos (by norm_num) m)⟩

/-- Negation `σ(j) = (j + 2^m) mod 2^(m+1)`. -/
def sigParam (m : ℕ) : Fin (2 ^ (m + 1)) → Fin (2 ^ (m + 1)) :=
  fun j => ⟨((j : ℕ) + 2 ^ m) % 2 ^ (m + 1), Nat.mod_lt _ (pow_pos (by norm_num) (m + 1))⟩

/-- The section `rep : Fin (2^m) ↪ Fin (2^(m+1))` (identity on values). -/
def repParam (m : ℕ) : Fin (2 ^ m) → Fin (2 ^ (m + 1)) :=
  fun y => ⟨(y : ℕ), lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m))⟩

/-- `q ∘ rep = id`. -/
theorem qParam_repParam (m : ℕ) (y : Fin (2 ^ m)) : qParam m (repParam m y) = y := by
  apply Fin.ext
  show (y : ℕ) % 2 ^ m = (y : ℕ)
  exact Nat.mod_eq_of_lt y.isLt

/-- `σ` preserves fibers: `q (σ (rep y)) = y`. -/
theorem qParam_sig_repParam (m : ℕ) (y : Fin (2 ^ m)) :
    qParam m (sigParam m (repParam m y)) = y := by
  apply Fin.ext
  have hlt : (y : ℕ) + 2 ^ m < 2 ^ (m + 1) := by have := y.isLt; rw [pow_succ]; omega
  show (((y : ℕ) + 2 ^ m) % 2 ^ (m + 1)) % 2 ^ m = (y : ℕ)
  rw [Nat.mod_eq_of_lt hlt, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

/-- The representative has nonzero value (`ω^j ≠ 0`). -/
theorem pParam_repParam_ne (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (y : Fin (2 ^ m)) :
    pParam m ω (repParam m y) ≠ 0 := by
  show ω ^ ((repParam m y : Fin (2 ^ (m + 1))) : ℕ) ≠ 0
  exact pow_ne_zero _ hω_ne

/-- The sibling has the negated value (`ω^(j+2^m) = ω^(2^m)·ω^j = -ω^j`). Uses `ω^(2^m) = -1`. -/
theorem pParam_sig_repParam (m : ℕ) (ω : BabyBear) (hω_neg : ω ^ (2 ^ m) = -1)
    (y : Fin (2 ^ m)) :
    pParam m ω (sigParam m (repParam m y)) = - pParam m ω (repParam m y) := by
  have hlt : (y : ℕ) + 2 ^ m < 2 ^ (m + 1) := by have := y.isLt; rw [pow_succ]; omega
  show ω ^ (((y : ℕ) + 2 ^ m) % 2 ^ (m + 1)) = - ω ^ (y : ℕ)
  rw [Nat.mod_eq_of_lt hlt, pow_add, hω_neg]; ring

/-- Every `x` is one of the two fiber representatives `{rep (q x), σ (rep (q x))}`. -/
theorem qParam_fiber (m : ℕ) (x : Fin (2 ^ (m + 1))) :
    x = repParam m (qParam m x) ∨ x = sigParam m (repParam m (qParam m x)) := by
  rcases Nat.lt_or_ge (x : ℕ) (2 ^ m) with hlt | hge
  · left
    apply Fin.ext
    show (x : ℕ) = (x : ℕ) % 2 ^ m
    exact (Nat.mod_eq_of_lt hlt).symm
  · right
    apply Fin.ext
    have hx : (x : ℕ) < 2 ^ (m + 1) := x.isLt
    have hx2 : (x : ℕ) < 2 ^ m * 2 := by rw [← pow_succ]; exact hx
    have hsub : (x : ℕ) - 2 ^ m < 2 ^ m := by omega
    have hmod : (x : ℕ) % 2 ^ m = (x : ℕ) - 2 ^ m := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
    show (x : ℕ) = (((x : ℕ) % 2 ^ m) + 2 ^ m) % 2 ^ (m + 1)
    rw [hmod, Nat.sub_add_cancel hge, Nat.mod_eq_of_lt hx]

/-- **The parameterized BabyBear FRI geometry** — every axiom PROVED generally in `m`. -/
noncomputable def friGeomParam (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (hω_neg : ω ^ (2 ^ m) = -1) :
    FriGeom BabyBear (Fin (2 ^ (m + 1))) (Fin (2 ^ m)) where
  σ := sigParam m
  q := qParam m
  p := pParam m ω
  rep := repParam m
  two_ne := by decide
  q_rep := qParam_repParam m
  q_σ_rep := qParam_sig_repParam m
  p_rep_ne := pParam_repParam_ne m ω hω_ne
  p_σ_rep := pParam_sig_repParam m ω hω_neg
  q_fiber := qParam_fiber m

/-! ## §2. The Reed-Solomon codes and the parameterized `FriSetup`.

`C = {x ↦ a + b·ω^x}` (deg `< 2`); `C' = {constants}` (deg `< 1`). Rate `= 2/2^(m+1) =
1/2^m`. The closure facts reuse `pParam_sig_repParam` / `pParam_repParam_ne` — general in `m`,
IDENTICAL algebra to brick 2. -/

/-- The domain code `C = {x ↦ a + b·ω^x}`. -/
noncomputable def codeC (m : ℕ) (ω : BabyBear) : Submodule BabyBear (Fin (2 ^ (m + 1)) → BabyBear) where
  carrier := {f | ∃ a b : BabyBear, f = fun x => a + b * pParam m ω x}
  zero_mem' := ⟨0, 0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by funext x; simp; ring⟩
  smul_mem' := by
    rintro c f ⟨a, b, rfl⟩
    exact ⟨c * a, c * b, by funext x; simp [mul_add]; ring⟩

/-- The folded code `C' = {constants}`. -/
noncomputable def codeC' (m : ℕ) : Submodule BabyBear (Fin (2 ^ m) → BabyBear) where
  carrier := {g | ∃ a : BabyBear, g = fun _ => a}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro f g ⟨a, rfl⟩ ⟨a', rfl⟩; exact ⟨a + a', rfl⟩
  smul_mem' := by rintro c f ⟨a, rfl⟩; exact ⟨c * a, rfl⟩

/-- **The parameterized BabyBear Reed-Solomon FRI setup** — closure PROVED, general in `m`. -/
noncomputable def friSetupParam (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (hω_neg : ω ^ (2 ^ m) = -1) :
    FriSetup BabyBear (Fin (2 ^ (m + 1))) (Fin (2 ^ m)) where
  geom := friGeomParam m ω hω_ne hω_neg
  C := codeC m ω
  C' := codeC' m
  unfold_closed := by
    rintro Ge ⟨ce, rfl⟩ Go ⟨co, rfl⟩
    exact ⟨ce, co, by funext x; simp only [unfoldF, friGeomParam]; ring⟩
  foldE_mem := by
    rintro f ⟨a, b, rfl⟩
    refine ⟨a, ?_⟩
    funext y
    have hps := pParam_sig_repParam m ω hω_neg y
    simp only [E, friGeomParam]
    rw [hps]
    rw [div_eq_iff (show (2 : BabyBear) ≠ 0 by decide)]
    ring
  foldO_mem := by
    rintro f ⟨a, b, rfl⟩
    refine ⟨b, ?_⟩
    funext y
    have hps := pParam_sig_repParam m ω hω_neg y
    have hpne : (2 : BabyBear) * pParam m ω (repParam m y) ≠ 0 :=
      mul_ne_zero (by decide) (pParam_repParam_ne m ω hω_ne y)
    simp only [O, friGeomParam]
    rw [hps]
    rw [div_eq_iff hpne]
    ring

/-! ## §3. The payoff — the field-generic PROVED lemmas, applied at any parameterized setup.

`friProximity_param` = `friProximity_discharge` APPLIED; `foldClose_param` =
`fold_close_of_two_alpha` APPLIED. No new hypothesis; the honest codeword is `2 + 3·ω^x`. -/

/-- An honest low-degree codeword `f = 2 + 3·ω^x` (`∈ C`, `a = 2`, `b = 3`). -/
noncomputable def fHonestParam (m : ℕ) (ω : BabyBear) : Fin (2 ^ (m + 1)) → BabyBear :=
  fun x => 2 + 3 * pParam m ω x

theorem fHonestParam_mem (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (hω_neg : ω ^ (2 ^ m) = -1) :
    fHonestParam m ω ∈ (friSetupParam m ω hω_ne hω_neg).C := ⟨2, 3, rfl⟩

/-- **`friProximity_discharge` APPLIED at the parameterized setup.** An accepting transcript
(query set `univ`, all checks pass, final codeword, generic challenge) discharges
`FriProximity`: `f` is a genuine codeword. Every argument supplied, none re-assumed. -/
theorem friProximity_param (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (hω_neg : ω ^ (2 ^ m) = -1) :
    FriProximity (friSetupParam m ω hω_ne hω_neg) 0 (fHonestParam m ω) :=
  friProximity_discharge (friSetupParam m ω hω_ne hω_neg)
    (f := fHonestParam m ω) (α := 0)
    (f' := Fold (friSetupParam m ω hω_ne hω_neg).geom 0 (fHonestParam m ω))
    Finset.univ (Finset.subset_univ _) (fun _ _ => rfl)
    (fold_complete (friSetupParam m ω hω_ne hω_neg) (fHonestParam_mem m ω hω_ne hω_neg) 0)
    (fun _ => fHonestParam_mem m ω hω_ne hω_neg)

/-- **`fold_close_of_two_alpha` APPLIED at the parameterized setup.** Two distinct challenges
(`0 ≠ 1`) both fold the honest codeword `0`-close, so the KEY LEMMA reconstructs it `4·0`-close.
The field-generic distance-preservation lemma, APPLIED. -/
theorem foldClose_param (m : ℕ) (ω : BabyBear) (hω_ne : ω ≠ 0) (hω_neg : ω ^ (2 ^ m) = -1) :
    closeN (friSetupParam m ω hω_ne hω_neg).C (4 * 0) (fHonestParam m ω) :=
  fold_close_of_two_alpha (friSetupParam m ω hω_ne hω_neg)
    (f := fHonestParam m ω) (α₁ := 0) (α₂ := 1) (by decide)
    (closeN_zero_iff_mem.mpr
      (fold_complete (friSetupParam m ω hω_ne hω_neg) (fHonestParam_mem m ω hω_ne hω_neg) 0))
    (closeN_zero_iff_mem.mpr
      (fold_complete (friSetupParam m ω hω_ne hω_neg) (fHonestParam_mem m ω hω_ne hω_neg) 1))

/-! ## §4. Instantiation A — the DEPLOYED RATE `1/8` at `m = 3` (`|L| = 16`).

`ω₁₆ = 196396260` is a concrete primitive `16`-th root of unity (`ω₁₆^8 = -1`, `decide`).
At `m = 3` the degree-`2` code on the size-`16` domain has rate `2/16 = 1/8` = the deployed
`log_blowup = 3`. This is the smallest domain realizing the DEPLOYED RATE. -/

/-- A concrete primitive `16`-th root of unity in BabyBear. -/
noncomputable def omega16 : BabyBear := 196396260

theorem omega16_ne : omega16 ≠ 0 := by decide
/-- `ω₁₆^(2^3) = ω₁₆^8 = -1` — a genuine order-`16` element (kernel numeral check). -/
theorem omega16_neg : omega16 ^ (2 ^ 3) = -1 := by decide

/-- **The DEPLOYED-RATE FRI setup**: `|L| = 2^4 = 16`, `|L²| = 8`, degree-`2` RS code,
rate `1/8`. -/
noncomputable def friSetupDeployedRate : FriSetup BabyBear (Fin (2 ^ 4)) (Fin (2 ^ 3)) :=
  friSetupParam 3 omega16 omega16_ne omega16_neg

/-- **Payoff at the deployed rate**: `friProximity_discharge` applied at `|L|=16`, rate `1/8`. -/
theorem deployedRate_friProximity :
    FriProximity friSetupDeployedRate 0 (fHonestParam 3 omega16) :=
  friProximity_param 3 omega16 omega16_ne omega16_neg

/-- **Payoff at the deployed rate**: `fold_close_of_two_alpha` applied at `|L|=16`, rate `1/8`. -/
theorem deployedRate_foldClose :
    closeN friSetupDeployedRate.C (4 * 0) (fHonestParam 3 omega16) :=
  foldClose_param 3 omega16 omega16_ne omega16_neg

/-! ### Teeth at the deployed rate — both polarities.

FIRES: the honest codeword folds into `C'` for every challenge (completeness) and is
`0`-close (above). BITES: a concrete FAR word is NOT in `C`, so the KEY LEMMA
(`exceptional_subsingleton`) forces its good-challenge set to be a subsingleton. -/

/-- The point-`0` indicator `f = ![1,0,…,0]` on the size-`16` domain. -/
noncomputable def fFar16 : Fin (2 ^ 4) → BabyBear := fun x => if (x : ℕ) = 0 then 1 else 0

/-- **`fFar16 ∉ C`.** If `fFar16 = a + b·ω₁₆^x`, evaluate at `x = 0` (`ω^0=1`), `x = 8`
(`ω^8 = -1`), `x = 1` (`ω^1 = ω₁₆`): `a+b = 1`, `a-b = 0` ⇒ `2b = 1` so `b ≠ 0`; then the
`x=1` row forces `ω₁₆ = -1`, false (`decide`). -/
theorem fFar16_not_mem : fFar16 ∉ friSetupDeployedRate.C := by
  rintro ⟨a, b, h⟩
  have h0 : (1 : BabyBear) = a + b * omega16 ^ 0 := by
    have := congrFun h ⟨0, by norm_num⟩; simpa [fFar16, pParam] using this
  have h8 : (0 : BabyBear) = a + b * omega16 ^ 8 := by
    have := congrFun h ⟨8, by norm_num⟩; simpa [fFar16, pParam] using this
  have h1 : (0 : BabyBear) = a + b * omega16 ^ 1 := by
    have := congrFun h ⟨1, by norm_num⟩; simpa [fFar16, pParam] using this
  rw [pow_zero] at h0
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, omega16_neg] at h8
  rw [pow_one] at h1
  -- h0 : 1 = a + b*1 ; h8 : 0 = a + b*(-1) ; h1 : 0 = a + b*ω₁₆
  have hb : (2 : BabyBear) * b = 1 := by linear_combination h8 - h0
  have hb0 : b ≠ 0 := by rintro rfl; rw [mul_zero] at hb; exact absurd hb (by decide)
  have hkey : b * (omega16 + 1) = 0 := by linear_combination h8 - h1
  rcases mul_eq_zero.mp hkey with hb' | hω
  · exact hb0 hb'
  · exact absurd (by linear_combination hω : omega16 = -1) (by decide)

/-- **Tooth (BITES): the KEY LEMMA at the deployed rate.** `fFar16` is far, so its
good-challenge set is a subsingleton (`exceptional_subsingleton` applied at `|L|=16`). -/
theorem fFar16_exceptional_subsingleton :
    {β : BabyBear | Fold friSetupDeployedRate.geom β fFar16 ∈ friSetupDeployedRate.C'}.Subsingleton :=
  exceptional_subsingleton friSetupDeployedRate fFar16_not_mem

/-- **Tooth (FIRES): completeness** — the honest codeword folds into `C'` for every challenge. -/
theorem deployedRate_fold_complete (α : BabyBear) :
    Fold friSetupDeployedRate.geom α (fHonestParam 3 omega16) ∈ friSetupDeployedRate.C' :=
  fold_complete friSetupDeployedRate (fHonestParam_mem 3 omega16 omega16_ne omega16_neg) α

/-! ## §5. Instantiation B — the full 2-adicity cap `|L| = 2^27` at `m = 26`.

`ω₂₇ = 440564289 = 31^15` is a primitive `2^27`-th root of unity (`31` generates
`BabyBear*`; `(p-1)/2^27 = 15`). Its order-`2^27` is proved by a 26-step squaring chain
`ω₂₇^(2^i)` (each step one numeral squaring by `decide`), ending `ω₂₇^(2^26) = -1`. The SAME
`friSetupParam` construction instantiates at `m = 26`: `|L| = 2^27` (brick 1's `2^27`
2-adicity cap), `|L²| = 2^26`. NOTE the degree-`2` code here has rate `2^-26`, NOT the
deployed `1/8` — this instance exhibits the DOMAIN reaching the cap, not the deployed rate. -/

/-- A concrete primitive `2^27`-th root of unity (`31^15 mod p`). -/
noncomputable def omega27 : BabyBear := 440564289

theorem omega27_ne : omega27 ≠ 0 := by decide

/-- **`ω₂₇^(2^26) = -1`** — order exactly `2^27`, by a 26-step iterated-squaring chain
(each `sᵢ₊₁ = sᵢ²` a single BabyBear numeral squaring the kernel decides). -/
theorem omega27_neg : omega27 ^ (2 ^ 26) = -1 := by
  have h1 : omega27 ^ (2 : ℕ) = 975630072 := by decide
  have h2 : omega27 ^ (4 : ℕ) = 1149491290 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h1]; decide
  have h3 : omega27 ^ (8 : ℕ) = 1003846038 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h2]; decide
  have h4 : omega27 ^ (16 : ℕ) = 1267047229 := by
    rw [show (16 : ℕ) = 8 * 2 from rfl, pow_mul, h3]; decide
  have h5 : omega27 ^ (32 : ℕ) = 570250684 := by
    rw [show (32 : ℕ) = 16 * 2 from rfl, pow_mul, h4]; decide
  have h6 : omega27 ^ (64 : ℕ) = 414040701 := by
    rw [show (64 : ℕ) = 32 * 2 from rfl, pow_mul, h5]; decide
  have h7 : omega27 ^ (128 : ℕ) = 195061667 := by
    rw [show (128 : ℕ) = 64 * 2 from rfl, pow_mul, h6]; decide
  have h8 : omega27 ^ (256 : ℕ) = 1049899240 := by
    rw [show (256 : ℕ) = 128 * 2 from rfl, pow_mul, h7]; decide
  have h9 : omega27 ^ (512 : ℕ) = 1559589183 := by
    rw [show (512 : ℕ) = 256 * 2 from rfl, pow_mul, h8]; decide
  have h10 : omega27 ^ (1024 : ℕ) = 1286330022 := by
    rw [show (1024 : ℕ) = 512 * 2 from rfl, pow_mul, h9]; decide
  have h11 : omega27 ^ (2048 : ℕ) = 1421947380 := by
    rw [show (2048 : ℕ) = 1024 * 2 from rfl, pow_mul, h10]; decide
  have h12 : omega27 ^ (4096 : ℕ) = 2009781145 := by
    rw [show (4096 : ℕ) = 2048 * 2 from rfl, pow_mul, h11]; decide
  have h13 : omega27 ^ (8192 : ℕ) = 1657000625 := by
    rw [show (8192 : ℕ) = 4096 * 2 from rfl, pow_mul, h12]; decide
  have h14 : omega27 ^ (16384 : ℕ) = 298008106 := by
    rw [show (16384 : ℕ) = 8192 * 2 from rfl, pow_mul, h13]; decide
  have h15 : omega27 ^ (32768 : ℕ) = 1282623253 := by
    rw [show (32768 : ℕ) = 16384 * 2 from rfl, pow_mul, h14]; decide
  have h16 : omega27 ^ (65536 : ℕ) = 1340477990 := by
    rw [show (65536 : ℕ) = 32768 * 2 from rfl, pow_mul, h15]; decide
  have h17 : omega27 ^ (131072 : ℕ) = 341742893 := by
    rw [show (131072 : ℕ) = 65536 * 2 from rfl, pow_mul, h16]; decide
  have h18 : omega27 ^ (262144 : ℕ) = 1753498361 := by
    rw [show (262144 : ℕ) = 131072 * 2 from rfl, pow_mul, h17]; decide
  have h19 : omega27 ^ (524288 : ℕ) = 1732600167 := by
    rw [show (524288 : ℕ) = 262144 * 2 from rfl, pow_mul, h18]; decide
  have h20 : omega27 ^ (1048576 : ℕ) = 397765732 := by
    rw [show (1048576 : ℕ) = 524288 * 2 from rfl, pow_mul, h19]; decide
  have h21 : omega27 ^ (2097152 : ℕ) = 1721589904 := by
    rw [show (2097152 : ℕ) = 1048576 * 2 from rfl, pow_mul, h20]; decide
  have h22 : omega27 ^ (4194304 : ℕ) = 760005850 := by
    rw [show (4194304 : ℕ) = 2097152 * 2 from rfl, pow_mul, h21]; decide
  have h23 : omega27 ^ (8388608 : ℕ) = 196396260 := by
    rw [show (8388608 : ℕ) = 4194304 * 2 from rfl, pow_mul, h22]; decide
  have h24 : omega27 ^ (16777216 : ℕ) = 1592366214 := by
    rw [show (16777216 : ℕ) = 8388608 * 2 from rfl, pow_mul, h23]; decide
  have h25 : omega27 ^ (33554432 : ℕ) = 1728404513 := by
    rw [show (33554432 : ℕ) = 16777216 * 2 from rfl, pow_mul, h24]; decide
  have h26 : omega27 ^ (67108864 : ℕ) = 2013265920 := by
    rw [show (67108864 : ℕ) = 33554432 * 2 from rfl, pow_mul, h25]; decide
  rw [show (2 ^ 26 : ℕ) = 67108864 from rfl, h26]; decide

/-- **The full-cap FRI setup**: `|L| = 2^27` (the 2-adicity cap), `|L²| = 2^26`, degree-`2`
RS code (rate `2^-26`). The SAME parameterized construction, at the largest BabyBear domain. -/
noncomputable def friSetupMaxDomain : FriSetup BabyBear (Fin (2 ^ 27)) (Fin (2 ^ 26)) :=
  friSetupParam 26 omega27 omega27_ne omega27_neg

/-- **Payoff at the 2^27 cap**: `friProximity_discharge` applied at `|L| = 2^27`. -/
theorem maxDomain_friProximity :
    FriProximity friSetupMaxDomain 0 (fHonestParam 26 omega27) :=
  friProximity_param 26 omega27 omega27_ne omega27_neg

/-- **Payoff at the 2^27 cap**: `fold_close_of_two_alpha` applied at `|L| = 2^27`. -/
theorem maxDomain_foldClose :
    closeN friSetupMaxDomain.C (4 * 0) (fHonestParam 26 omega27) :=
  foldClose_param 26 omega27 omega27_ne omega27_neg

/-! ## §Axiom hygiene — the payoff + teeth rest only on the kernel axioms (no `sorry`, no
smuggled hardness; the `friProximity_discharge`/`fold_close_of_two_alpha` content is imported
PROVED and merely instantiated at the deployed field, deployed rate, and 2-adicity cap). -/

#assert_axioms deployedRate_friProximity
#assert_axioms deployedRate_foldClose
#assert_axioms fFar16_exceptional_subsingleton
#assert_axioms maxDomain_friProximity
#assert_axioms maxDomain_foldClose
#assert_axioms omega27_neg

end Dregg2.Circuit.BabyBearFriDeployed
