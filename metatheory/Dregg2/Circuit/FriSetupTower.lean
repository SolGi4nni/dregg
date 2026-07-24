/-
# `Dregg2.Circuit.FriSetupTower` — ⚑ THE WELDED MULTI-LAYER `FriSetupK` TOWER (ladder rung L5):
the layer-linked setup family the L2 header named as missing, built at the deployed arity-8
fold schedule, with `ChainStepIdx` genuinely instantiated at FIVE real layers.

**THE GAP (verbatim from `FriChainStepIdx.lean:63-71`).** "No welded setup TOWER. A deployed
`L`-layer instance of `ChainStepIdx` needs a family `S : Fin L → FriSetupK` with
`(S i).C' = (S (i+1)).C` (the folded code of layer `i` IS the domain code of layer `i+1`) …
`FriFoldArity` provides ONE setup (`friSetupK8`, `|ι| = 16, |κ| = 2`) and its §4 instance cannot
even take a second arity-8 step (`|κ| = 2 < 8`). §6 therefore fires at ONE layer." This file
closes that: `towerS` (§5) is the welded family, `tower_link` the layer link, and
`tower_chain_far_survival` (§7) runs `chain_far_survival_idx` (`FriChainStepIdx:416`) through
FIVE real arity-8 layers of the deployed shape — not the toy.

**The deployed schedule, paired honestly.** The arity-8 knob is `PROD_FRI_MAX_LOG_ARITY = 3`
(`circuit/src/plonky3_prover.rs:98`, cited at `FriFoldArity.lean:4-5`): the shipped production
fold is 8-to-1 per round. Its OWN height pairing is `|D⁽⁰⁾| = 2^16 · 2^3 = 2^19`
(`fri_trace_height_measure.rs:133`, `DEPLOYED_WORST_LOG_D0 = 19` — the trace-height floor at
the `log_blowup = 3` config's own blowup). ⚠ `FriDeployedHeightPairing.lean:42` proves the
OTHER deployed pairing — the wrap-path RUNNING fold — is the arity-**2**, `lb = 6` config at
`|D⁽⁰⁾| = 2^22`, and that mixing heights across configs is exactly the sin that file localizes.
So this tower is the **arity-8 production schedule at its own pairing**: domain
`2^19 → 2^16 → 2^13 → 2^10 → 2^7 → 2^4` (shrinks by the fold arity 8 each round), degree
`2^16 → 2^13 → … → 2` (divides by 8 each round), rate `2^-3` at every layer, five welded
layers — depth 5 is where the schedule exhausts the degree, not a shortcut. The layer
constructor `towerLayer` (§3) is ARITY-GENERIC, so the arity-2/`lb 6`/`2^22` wrap tower is the
same constructor at `n = 2` — stated as reachable, NOT landed here.

**What "welded" means here (read before trusting the link).** Each layer's `C'` is DEFINED as
the next layer's RS code (one root chain: layer `i` uses `wchain (i+1)`, and
`wchain (i+2) = wchain (i+1) ^ 8` definitionally), so `tower_link` is definitionally tight —
the CONTENT is that this `C'` discharges `FriSetupK`'s two closure obligations
(`unfold_closed`, `foldC_mem`) at every layer, which pins `C'` from BOTH sides: §8 proves a
HALVED-degree `C'` fails `foldC_mem` (`canary_halved_degree_unbuildable`), an INFLATED-degree
`C'` fails `unfold_closed` (`canary_inflated_degree_unbuildable` — its reassembled "codeword"
is LITERALLY the far word), and the link EQUATION itself rejects the tampered code
(`canary_halved_degree_link`). A wrong-SIZE domain at a layer is rejected by the TYPES
(`κ_i = ι_{i+1}` is in `towerS`'s signature). The deployed fold schedule DOES satisfy the
link — no RS-shape obstruction; folding stays in one code family with the root advanced to
`ω^8`.

**Honest scope.**
  * A TOTAL `ℕ`-indexed tower of arity-8 setups is IMPOSSIBLE, not merely missing: a
    `FriGeomK _ ι κ 8` needs 8 fiber representatives with pairwise-DISTINCT values over every
    point of `κ`, so `|ι| ≥ 8` whenever `κ` is inhabited — fixed-arity towers have finite
    depth. The family here is `∀ i, i < 5 → FriSetupK …` (the `Fin L` shape the L2 header
    itself specified); the `ChainStepIdx` carrier `WT` is total over `ℕ` with a trivial tail,
    exactly like `FriChainStepIdx` §6's `W8`.
  * The radius schedule instantiated is `d = 0` (far = "not a codeword"), as in the L2 §6
    single-layer instance; the per-layer cap is `goodδ_card_lt`'s `n − 1 = 7`
    (`FriChainStepIdx:460`). What the big domains UNLOCK (not done here):
    `FriPositiveRadiusPayment` proved positive-radius farness UNINHABITED at `|ι| = 16`; at
    `|ι| = 2^19` the `n²·d` radius has room — the positive-`d` schedule over this tower is the
    natural next rung.
  * The survival bound is the L2 corollary's `n·b/|R| = 5·7/|BabyBear|` — a ROM/FS statement
    about the honest-fold word evolution. It is NOT a soundness claim against the deployed
    prover (no extractor, no Merkle binding), and the FRI floor posture is untouched.

**Root chain (computed offline, machine-checked here).** `w22 = 570250684 = 31^480 mod p` has
exact order `2^22` (`w22_ord`) via a 21-step squaring chain — each step ONE kernel
multiplication, no giant `pow`, no domain enumeration anywhere (the geometry and the DFT
functional arguments are fully symbolic, which is what lets the tower live at the real `2^19`).
`wchain 6 = omega16` (`wchain_six`): the chain lands EXACTLY on `BabyBearFriDeployed.omega16`,
the root the `friSetupK8` toy is built from — the terminal code is `rsCode (2^4) 2 omega16`
(`tower_bottom_is_omega16_code`).

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no new axiom, no
`native_decide`. Imports green at HEAD: `FriChainStepIdx` (and through it `FriFoldArity`,
`FriAdversaryObject`, `RomCounting`), `FriDeployedHeightPairing` (cited for the pairing facts
only), `Dregg2.Tactics`.
-/
import Dregg2.Circuit.FriChainStepIdx
import Dregg2.Circuit.FriDeployedHeightPairing
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriSetupTower

open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem disagree)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.FriChainStepIdx
open Dregg2.Circuit.FriAdversaryObject
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.BabyBearFriDeployed (omega16)
open scoped BigOperators Matrix

/-! ## §1 — the arity split: `Fin n × Fin D' ≃ Fin (n·D')` by `(a, b) ↦ a + n·b`.

The digit decomposition every RS fold rests on: a degree-`< n·D'` polynomial is `n` interleaved
degree-`< D'` polynomials in `X^n`. -/

/-- `(a, b) ↦ a + n·b` as an equivalence `Fin n × Fin D' ≃ Fin (n * D')`. -/
def arityPairEquiv (n D' : ℕ) (hn : 0 < n) : Fin n × Fin D' ≃ Fin (n * D') where
  toFun p := ⟨(p.1 : ℕ) + n * (p.2 : ℕ), by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    calc a + n * b < n + n * b := by omega
      _ = n * (b + 1) := by ring
      _ ≤ n * D' := Nat.mul_le_mul_left n hb⟩
  invFun j := (⟨(j : ℕ) % n, Nat.mod_lt _ hn⟩, ⟨(j : ℕ) / n, Nat.div_lt_of_lt_mul j.isLt⟩)
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h1 : (a + n * b) % n = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have h2 : (a + n * b) / n = b := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ha, zero_add]
    simp only [Prod.mk.injEq, Fin.mk.injEq]
    exact ⟨h1, h2⟩
  right_inv := fun j => Fin.ext (Nat.mod_add_div _ _)

@[simp] theorem arityPairEquiv_coe {n D' : ℕ} (hn : 0 < n) (a : Fin n) (b : Fin D') :
    ((arityPairEquiv n D' hn (a, b)) : ℕ) = (a : ℕ) + n * (b : ℕ) := rfl

/-- Splitting a `Fin (n·D')` sum along the digit decomposition. -/
theorem sum_arity_split {M : Type*} [AddCommMonoid M] (n D' : ℕ) (hn : 0 < n)
    (g : Fin (n * D') → M) :
    ∑ j, g j = ∑ a : Fin n, ∑ b : Fin D', g (arityPairEquiv n D' hn (a, b)) := by
  rw [← Equiv.sum_comp (arityPairEquiv n D' hn) g, Fintype.sum_prod_type]

/-! ## §2 — the generic layer geometry and the RS code family. -/

section Generic

variable {F : Type*} [Field F] [DecidableEq F]

private theorem pow_sub_eq_one {ω : F} (hω0 : ω ≠ 0) {a b : ℕ} (hab : a ≤ b)
    (h : ω ^ a = ω ^ b) : ω ^ (b - a) = 1 := by
  have hb' : ω ^ b = ω ^ a * ω ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
  refine mul_left_cancel₀ (pow_ne_zero a hω0) ?_
  rw [mul_one, ← hb']
  exact h.symm

/-- Powers of a root of exact order `N` are injective below `N` (field cancellation — `F` is
not a cancel monoid because of `0`, but `ω ≠ 0` follows from having positive order). -/
theorem pow_inj_of_orderOf {ω : F} {N a b : ℕ} (hord : orderOf ω = N) (hN : 0 < N)
    (ha : a < N) (hb : b < N) (h : ω ^ a = ω ^ b) : a = b := by
  have hω0 : ω ≠ 0 := by
    intro h0
    have h1 : ω ^ N = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
    rw [h0, zero_pow (by omega : N ≠ 0)] at h1
    exact one_ne_zero h1.symm
  rcases le_total a b with hab | hab
  · have hdvd := orderOf_dvd_of_pow_eq_one (pow_sub_eq_one hω0 hab h)
    rw [hord] at hdvd
    have h0 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega
  · have hdvd := orderOf_dvd_of_pow_eq_one (pow_sub_eq_one hω0 hab h.symm)
    rw [hord] at hdvd
    have h0 : a - b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    omega

/-- **The generic arity-`n` layer geometry** on the cyclic domain `Fin (n·M)` with point map
`x ↦ ω^x` for a root `ω` of exact order `n·M`: quotient `x ↦ x mod M`, representatives
`reps y i = y + M·i`. Fiber-value distinctness comes from the ORDER, not from enumeration — so
the construction scales to the deployed `2^19` domain with zero kernel enumeration. -/
def towerGeom (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (ω : F) (hord : orderOf ω = n * M) :
    FriGeomK F (Fin (n * M)) (Fin M) n where
  q := fun x => ⟨(x : ℕ) % M, Nat.mod_lt _ hM⟩
  p := fun x => ω ^ (x : ℕ)
  reps := fun y i => ⟨(y : ℕ) + M * (i : ℕ), by
    obtain ⟨y, hy⟩ := y; obtain ⟨i, hi⟩ := i
    calc y + M * i < M + M * i := by omega
      _ = M * (i + 1) := by ring
      _ ≤ M * n := Nat.mul_le_mul_left M hi
      _ = n * M := Nat.mul_comm M n⟩
  q_reps := fun y i => Fin.ext (by
    show ((y : ℕ) + M * (i : ℕ)) % M = (y : ℕ)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt])
  p_reps_inj := by
    intro y i i' h
    have hlt : ∀ k : Fin n, (y : ℕ) + M * (k : ℕ) < n * M := by
      intro k
      calc (y : ℕ) + M * (k : ℕ) < M + M * (k : ℕ) := by omega
        _ = M * ((k : ℕ) + 1) := by ring
        _ ≤ M * n := Nat.mul_le_mul_left M k.isLt
        _ = n * M := Nat.mul_comm M n
    have heq : (y : ℕ) + M * (i : ℕ) = (y : ℕ) + M * (i' : ℕ) :=
      pow_inj_of_orderOf hord (Nat.mul_pos hn hM) (hlt i) (hlt i') h
    have hMi : M * (i : ℕ) = M * (i' : ℕ) := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hM hMi)
  q_fiber := fun x => ⟨⟨(x : ℕ) / M, by
      have hx : (x : ℕ) < M * n := by rw [Nat.mul_comm M n]; exact x.isLt
      exact Nat.div_lt_of_lt_mul hx⟩,
    Fin.ext (by
      show (x : ℕ) = (x : ℕ) % M + M * ((x : ℕ) / M)
      rw [Nat.mod_add_div])⟩

/-- **The generic RS code**: degree-`< D` polynomials evaluated on `x ↦ ω^x` over `Fin N`.
`rsCode 16 8 omega16` is the toy `codeC8`'s shape; `rsCode (2^19) (2^16) (wchain 1)` is the
deployed layer-0 domain code. -/
def rsCode (N D : ℕ) (ω : F) : Submodule F (Fin N → F) where
  carrier := {f | ∃ c : Fin D → F,
    f = fun x : Fin N => ∑ j : Fin D, c j * (ω ^ (x : ℕ)) ^ (j : ℕ)}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨c + c', ?_⟩
    funext x
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp [add_mul])
  smul_mem' := by
    rintro a f ⟨c, rfl⟩
    refine ⟨a • c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])

theorem mem_rsCode {N D : ℕ} {ω : F} {f : Fin N → F} :
    f ∈ rsCode N D ω
      ↔ ∃ c : Fin D → F, f = fun x : Fin N => ∑ j : Fin D, c j * (ω ^ (x : ℕ)) ^ (j : ℕ) :=
  Iff.rfl

/-- The monomial word `x ↦ (ω^x)^k`. -/
def monoW (N k : ℕ) (ω : F) : Fin N → F := fun x => (ω ^ (x : ℕ)) ^ k

/-- Low-degree monomials are codewords. -/
theorem monoW_mem {N D k : ℕ} (ω : F) (hk : k < D) : monoW N k ω ∈ rsCode N D ω := by
  refine ⟨fun j => if j = (⟨k, hk⟩ : Fin D) then 1 else 0, ?_⟩
  funext x
  simp only [monoW]
  symm
  rw [Finset.sum_congr rfl (fun j _ => by rw [ite_mul, one_mul, zero_mul]),
    Finset.sum_ite_eq' Finset.univ (⟨k, hk⟩ : Fin D) (fun j => (ω ^ (x : ℕ)) ^ (j : ℕ))]
  simp

/-- **The DFT-functional refutation: a monomial of degree in `[D, N)` is NOT in the
degree-`< D` code**, for `ω` of exact order `N` with `N ≠ 0` in `F`. The functional
`φ f = Σ_x ω^((N−k)·x) · f x` kills every monomial below `D` (a full-period geometric sum with
ratio `ω^(N−k+j) ≠ 1`) and reads `N ≠ 0` on the degree-`k` monomial. Fully symbolic — no
domain enumeration — so it fires at `N = 2^19`. -/
theorem monoW_not_mem {N D k : ℕ} (ω : F) (hord : orderOf ω = N) (hDk : D ≤ k) (hkN : k < N)
    (hN : (N : F) ≠ 0) : monoW N k ω ∉ rsCode N D ω := by
  intro hmem
  obtain ⟨c, hc⟩ := hmem
  have hωN : ω ^ N = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  -- φ on the monomial itself: every term is 1, the sum is N.
  have hmono : ∑ x : Fin N, (ω ^ (N - k)) ^ (x : ℕ) * monoW N k ω x = (N : F) := by
    have h1 : ∀ x : Fin N, (ω ^ (N - k)) ^ (x : ℕ) * monoW N k ω x = 1 := by
      intro x
      simp only [monoW]
      rw [← pow_mul, ← pow_mul, ← pow_add]
      have he : (N - k) * (x : ℕ) + (x : ℕ) * k = N * (x : ℕ) := by
        rw [Nat.sub_mul, Nat.mul_comm (x : ℕ) k]
        exact Nat.sub_add_cancel (Nat.mul_le_mul_right _ (le_of_lt hkN))
      rw [he, pow_mul, hωN, one_pow]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- φ on the code: every monomial below D dies by the geometric sum.
  have hcode : ∑ x : Fin N,
      (ω ^ (N - k)) ^ (x : ℕ) * (∑ j : Fin D, c j * (ω ^ (x : ℕ)) ^ (j : ℕ)) = 0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hterm : ∀ x : Fin N, (ω ^ (N - k)) ^ (x : ℕ) * (c j * (ω ^ (x : ℕ)) ^ (j : ℕ))
        = c j * (ω ^ (N - k + (j : ℕ))) ^ (x : ℕ) := by
      intro x
      calc (ω ^ (N - k)) ^ (x : ℕ) * (c j * (ω ^ (x : ℕ)) ^ (j : ℕ))
          = c j * (ω ^ ((N - k) * (x : ℕ)) * ω ^ ((x : ℕ) * (j : ℕ))) := by
            rw [← pow_mul, ← pow_mul]; ring
        _ = c j * ω ^ ((N - k + (j : ℕ)) * (x : ℕ)) := by
            rw [← pow_add]
            congr 1
            ring
        _ = c j * (ω ^ (N - k + (j : ℕ))) ^ (x : ℕ) := by rw [pow_mul]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    have hj : (j : ℕ) < D := j.isLt
    have he_pos : 0 < N - k + (j : ℕ) := by omega
    have he_lt : N - k + (j : ℕ) < N := by omega
    have hr_ne : ω ^ (N - k + (j : ℕ)) ≠ 1 := by
      intro h1
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at hdvd
      exact absurd (Nat.le_of_dvd he_pos hdvd) (not_le.mpr he_lt)
    have hrN : (ω ^ (N - k + (j : ℕ))) ^ N = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hωN, one_pow]
    rw [Fin.sum_univ_eq_sum_range (fun t => (ω ^ (N - k + (j : ℕ))) ^ t) N,
      geom_sum_eq hr_ne N, hrN, sub_self, zero_div, mul_zero]
  have hswap : ∑ x : Fin N, (ω ^ (N - k)) ^ (x : ℕ) * monoW N k ω x
      = ∑ x : Fin N, (ω ^ (N - k)) ^ (x : ℕ) * (∑ j : Fin D, c j * (ω ^ (x : ℕ)) ^ (j : ℕ)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hc]
  apply hN
  rw [← hmono, hswap]
  exact hcode

/-- The fold-variable congruence: over the layer geometry, `(ω^x)^n` depends only on
`x mod M` — it IS the next layer's point value. -/
theorem pow_n_eq (n M : ℕ) (ω : F) (hord : orderOf ω = n * M) (x : Fin (n * M)) :
    (ω ^ ((x : ℕ))) ^ n = (ω ^ n) ^ ((x : ℕ) % M) := by
  have hωNM : ω ^ (n * M) = 1 := by rw [← hord]; exact pow_orderOf_eq_one ω
  have hsplit : (x : ℕ) * n = (x : ℕ) % M * n + n * M * ((x : ℕ) / M) := by
    conv_lhs => rw [← Nat.mod_add_div (x : ℕ) M]
    ring
  rw [← pow_mul, hsplit, pow_add, pow_mul ω (n * M), hωNM, one_pow, mul_one,
    Nat.mul_comm ((x : ℕ) % M) n, pow_mul]

/-! ## §3 — decomposition uniqueness and the welded layer constructor. -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}

/-- **Decomposition inverts reassembly** (uniqueness through the fiber Vandermonde): the `j`-th
component of `reassemble G Df` is `Df j`. This is what lets us READ OFF the components of a
codeword once written in reassembled form — the engine of `foldC_mem` at every tower layer,
and of the canaries. -/
theorem Cj_reassemble (G : FriGeomK F ι κ n) (Df : Fin n → κ → F) (j : Fin n) :
    Cj G j (reassemble G Df) = fun y => Df j y := by
  funext y
  have hfv : fvec G (reassemble G Df) y = fiberV G y *ᵥ (fun k => Df k y) := by
    funext i
    rw [mulVec_eq]
    show reassemble G Df (G.reps y i) = ∑ k, fiberV G y i k * Df k y
    simp only [reassemble]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [G.q_reps, fiberV, Matrix.vandermonde_apply]
  show comps G (reassemble G Df) y j = Df j y
  rw [comps, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (fiberV_isUnit_det G y),
    Matrix.one_mulVec]

/-- **The layer identity**: reassembling `n` degree-`< D'` polynomials in the folded variable
is exactly the degree-`< n·D'` polynomial with digit-interleaved coefficients. Both closure
obligations of the welded layer are the two readings of this one identity. -/
theorem reassemble_tower (n M D' : ℕ) (hn : 0 < n) (hM : 0 < M) (ω : F)
    (hord : orderOf ω = n * M) (cf : Fin n → Fin D' → F) :
    reassemble (towerGeom n M hn hM ω hord)
        (fun a y => ∑ b : Fin D', cf a b * ((ω ^ n) ^ (y : ℕ)) ^ (b : ℕ))
      = fun x : Fin (n * M) => ∑ a : Fin n, ∑ b : Fin D',
          cf a b * (ω ^ (x : ℕ)) ^ ((a : ℕ) + n * (b : ℕ)) := by
  funext x
  simp only [reassemble]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (ω ^ (x : ℕ)) ^ (a : ℕ) * ∑ b : Fin D', cf a b * ((ω ^ n) ^ ((x : ℕ) % M)) ^ (b : ℕ)
      = ∑ b : Fin D', cf a b * (ω ^ (x : ℕ)) ^ ((a : ℕ) + n * (b : ℕ))
  rw [← pow_n_eq n M ω hord x, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← pow_mul, pow_add]
  ring

/-- **THE WELDED LAYER CONSTRUCTOR** — a genuine `FriSetupK` at arity `n` on the cyclic domain
`Fin (n·M)`: domain code degree `< n·D'` in root `ω`, folded code degree `< D'` in the advanced
root `ω^n`. Both closure obligations are PROVED from the layer identity + decomposition
uniqueness; nothing about the fold is assumed. The tower is this constructor iterated down the
root chain. -/
noncomputable def towerLayer (n M D' : ℕ) (hn : 0 < n) (hM : 0 < M) (ω : F)
    (hord : orderOf ω = n * M) : FriSetupK F (Fin (n * M)) (Fin M) n where
  geom := towerGeom n M hn hM ω hord
  C := rsCode (n * M) (n * D') ω
  C' := rsCode M D' (ω ^ n)
  unfold_closed := by
    intro Df hDf
    have hDf' : ∀ a, ∃ c : Fin D' → F,
        Df a = fun y : Fin M => ∑ b : Fin D', c b * ((ω ^ n) ^ (y : ℕ)) ^ (b : ℕ) :=
      fun a => hDf a
    choose cf hcf using hDf'
    have hDfeq : Df = fun (a : Fin n) (y : Fin M) =>
        ∑ b : Fin D', cf a b * ((ω ^ n) ^ (y : ℕ)) ^ (b : ℕ) := by
      funext a
      exact hcf a
    rw [hDfeq, reassemble_tower]
    refine ⟨fun j => cf ((arityPairEquiv n D' hn).symm j).1 ((arityPairEquiv n D' hn).symm j).2,
      ?_⟩
    funext x
    rw [sum_arity_split n D' hn
      (fun j => cf ((arityPairEquiv n D' hn).symm j).1 ((arityPairEquiv n D' hn).symm j).2
        * (ω ^ (x : ℕ)) ^ ((j : ℕ)))]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
      simp only [Equiv.symm_apply_apply, arityPairEquiv_coe]
  foldC_mem := by
    intro f hf j
    obtain ⟨c, rfl⟩ := hf
    have hre : (fun x : Fin (n * M) => ∑ k : Fin (n * D'), c k * (ω ^ (x : ℕ)) ^ ((k : ℕ)))
        = reassemble (towerGeom n M hn hM ω hord)
            (fun a y => ∑ b : Fin D',
              c (arityPairEquiv n D' hn (a, b)) * ((ω ^ n) ^ (y : ℕ)) ^ (b : ℕ)) := by
      rw [reassemble_tower]
      funext x
      rw [sum_arity_split n D' hn (fun k => c k * (ω ^ (x : ℕ)) ^ ((k : ℕ)))]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        simp only [arityPairEquiv_coe]
    rw [hre, Cj_reassemble]
    exact ⟨fun b => c (arityPairEquiv n D' hn (j, b)), rfl⟩

/-- Reassembling a single degree-`b` monomial (in slot 0) yields the degree-`n·b` monomial —
the canaries' witness engine. -/
theorem reassemble_single_mono (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (ω : F)
    (hord : orderOf ω = n * M) (b : ℕ) :
    reassemble (towerGeom n M hn hM ω hord)
        (fun a => if a = (⟨0, hn⟩ : Fin n) then monoW M b (ω ^ n) else 0)
      = monoW (n * M) (n * b) ω := by
  funext x
  simp only [reassemble]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)
    (fun k _ hk => by rw [if_neg hk, Pi.zero_apply, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [if_pos rfl]
  show (ω ^ (x : ℕ)) ^ ((0 : ℕ)) * ((ω ^ n) ^ ((x : ℕ) % M)) ^ b = (ω ^ (x : ℕ)) ^ (n * b)
  rw [pow_zero, one_mul, ← pow_n_eq n M ω hord x, ← pow_mul]

/-- The `0`-th component of the degree-`n·b` monomial is the degree-`b` monomial in the folded
variable. -/
theorem Cj_monoW (n M : ℕ) (hn : 0 < n) (hM : 0 < M) (ω : F) (hord : orderOf ω = n * M)
    (b : ℕ) :
    Cj (towerGeom n M hn hM ω hord) (⟨0, hn⟩ : Fin n) (monoW (n * M) (n * b) ω)
      = monoW M b (ω ^ n) := by
  rw [← reassemble_single_mono n M hn hM ω hord b, Cj_reassemble]
  funext y
  rw [if_pos rfl]

end Generic

/-! ## §4 — the BabyBear root chain: `w22` of order `2^22`, checked by 21 squarings. -/

/-- `31^480 mod p` — `31` generates `BabyBear^×` (order `15·2^27`), so this has exact order
`2^22`. The order is MACHINE-CHECKED below via the squaring chain, not trusted from this
comment. -/
noncomputable def w22 : BabyBear := 570250684

/-- The squaring chain `chainVal k = w22^(2^k)` as literals — verified by `chainVal_sq` +
`w22_pow_two_pow`; each step is ONE kernel multiplication mod `p`, so no giant `pow`. -/
noncomputable def chainVal : ℕ → BabyBear
  | 0 => 570250684
  | 1 => 414040701
  | 2 => 195061667
  | 3 => 1049899240
  | 4 => 1559589183
  | 5 => 1286330022
  | 6 => 1421947380
  | 7 => 2009781145
  | 8 => 1657000625
  | 9 => 298008106
  | 10 => 1282623253
  | 11 => 1340477990
  | 12 => 341742893
  | 13 => 1753498361
  | 14 => 1732600167
  | 15 => 397765732
  | 16 => 1721589904
  | 17 => 760005850
  | 18 => 196396260
  | 19 => 1592366214
  | 20 => 1728404513
  | 21 => 2013265920
  | _ + 22 => 0

theorem chainVal_sq : ∀ k, k < 21 → chainVal k * chainVal k = chainVal (k + 1) := by decide

theorem w22_pow_two_pow : ∀ k, k ≤ 21 → w22 ^ ((2 : ℕ) ^ k) = chainVal k := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, pow_one]; rfl
  | succ k ih =>
      intro hk
      rw [pow_succ, pow_mul, ih (by omega), pow_two]
      exact chainVal_sq k (by omega)

theorem w22_ord : orderOf w22 = 2 ^ 22 := by
  have h21 : w22 ^ ((2 : ℕ) ^ 21) = -1 := by
    rw [w22_pow_two_pow 21 le_rfl]; decide
  have hne : ¬ w22 ^ ((2 : ℕ) ^ 21) = 1 := by rw [h21]; decide
  have hone : w22 ^ ((2 : ℕ) ^ (21 + 1)) = 1 := by
    rw [pow_succ, pow_mul, h21, neg_one_sq]
  exact orderOf_eq_prime_pow hne hone

/-- The tower's root chain: `wchain (i+1) = (wchain i)^8` — DEFINITIONALLY, which is what makes
every layer link `rfl`-tight. -/
noncomputable def wchain : ℕ → BabyBear
  | 0 => w22
  | i + 1 => wchain i ^ 8

theorem wchain_eq : ∀ i, wchain i = w22 ^ ((8 : ℕ) ^ i)
  | 0 => by rw [wchain, pow_zero, pow_one]
  | i + 1 => by rw [wchain, wchain_eq i, ← pow_mul, ← pow_succ]

/-- Every chain root's exact order, from ONE squaring-chain fact — symbolic in `i`. -/
theorem wchain_ord (i : ℕ) (hi : i ≤ 7) : orderOf (wchain i) = 2 ^ (22 - 3 * i) := by
  have hneg : wchain i ^ ((2 : ℕ) ^ (21 - 3 * i)) = -1 := by
    rw [wchain_eq, show (8 : ℕ) ^ i = 2 ^ (3 * i) from by rw [pow_mul]; norm_num,
      ← pow_mul, ← pow_add, show 3 * i + (21 - 3 * i) = 21 from by omega,
      w22_pow_two_pow 21 le_rfl]
    decide
  have hne : ¬ wchain i ^ ((2 : ℕ) ^ (21 - 3 * i)) = 1 := by rw [hneg]; decide
  have hone : wchain i ^ ((2 : ℕ) ^ ((21 - 3 * i) + 1)) = 1 := by
    rw [pow_succ, pow_mul, hneg, neg_one_sq]
  rw [orderOf_eq_prime_pow hne hone]
  congr 1
  omega

/-- **The chain lands on the tree's deployed root**: `wchain 6 = omega16`
(`BabyBearFriDeployed.omega16 = 196396260`), the root `friSetupK8` and the whole toy line are
built from. The tower and the toy share one root system. -/
theorem wchain_six : wchain 6 = omega16 := by
  rw [wchain_eq, show (8 : ℕ) ^ 6 = 2 ^ 18 from by norm_num,
    w22_pow_two_pow 18 (by norm_num)]
  decide

/-! ## §5 — ⚑ THE TOWER: five welded arity-8 layers at the deployed production schedule. -/

/-- The deployed domain schedule: `|D⁽ⁱ⁾| = 2^(19 − 3i)` — `2^19` at the top
(`DEPLOYED_WORST_LOG_D0 = 19`, the `lb = 3` config's own pairing), shrinking by the fold
arity `8` each round. -/
def twSz (i : ℕ) : ℕ := 2 ^ (19 - 3 * i)

/-- **THE WELDED SETUP TOWER** — the family `FriChainStepIdx:63-71` named as missing: five
arity-8 `FriSetupK`s, layer `i` on `(Fin (twSz i), Fin (twSz (i+1)))` with domain code degree
`2^(16−3i)` (rate `2^-3` at every layer, the `lb = 3` blowup) and root `wchain (i+1)`. The
type-level weld `κ_i = ι_{i+1}` is in the SIGNATURE; the code-level weld is `tower_link`. -/
noncomputable def towerS :
    ∀ i : ℕ, i < 5 → FriSetupK BabyBear (Fin (twSz i)) (Fin (twSz (i + 1))) 8
  | 0, _ => towerLayer 8 (2 ^ 16) (2 ^ 13) (by norm_num) (by norm_num) (wchain 1)
      (by rw [wchain_ord 1 (by norm_num)]; norm_num)
  | 1, _ => towerLayer 8 (2 ^ 13) (2 ^ 10) (by norm_num) (by norm_num) (wchain 2)
      (by rw [wchain_ord 2 (by norm_num)]; norm_num)
  | 2, _ => towerLayer 8 (2 ^ 10) (2 ^ 7) (by norm_num) (by norm_num) (wchain 3)
      (by rw [wchain_ord 3 (by norm_num)]; norm_num)
  | 3, _ => towerLayer 8 (2 ^ 7) (2 ^ 4) (by norm_num) (by norm_num) (wchain 4)
      (by rw [wchain_ord 4 (by norm_num)]; norm_num)
  | 4, _ => towerLayer 8 (2 ^ 4) 2 (by norm_num) (by norm_num) (wchain 5)
      (by rw [wchain_ord 5 (by norm_num)]; norm_num)
  | n + 5, h => absurd h (by omega)

/-- **⚑ THE LAYER LINK** — `(S i).C' = (S (i+1)).C` at every weld of the deployed schedule: the
folded code of layer `i` IS the domain code of layer `i+1` (degree `2^(13−3i)`, root
`wchain (i+1) ^ 8 = wchain (i+2)`). Definitionally tight by construction — and §8 proves the
tightness is LOAD-BEARING: neither a smaller nor a larger `C'` can discharge the closure
obligations that bound this construction. -/
theorem tower_link : ∀ (i : ℕ) (h : i < 5) (h' : i + 1 < 5),
    (towerS i h).C' = (towerS (i + 1) h').C := by
  intro i h h'
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => exact absurd h' (by omega)

/-- The terminal code carries the tree's own deployed root: layer 4 folds into
`rsCode (2^4) 2 omega16` — degree-`< 2` residuals on the `omega16` domain, the exact root
system of the `friSetupK8` toy. -/
theorem tower_bottom_is_omega16_code (h : (4 : ℕ) < 5) :
    (towerS 4 h).C' = rsCode (2 ^ 4) 2 omega16 :=
  congrArg (rsCode (2 ^ 4) 2) wchain_six

/-! ## §6 — the `ChainStepIdx` instantiation: the tower AS the indexed chain, five real
layers. -/

/-- The layer word carriers — total over `ℕ` (trivial `Fin 1` tail past the schedule), so the
indexed machinery applies verbatim. -/
def WT : ℕ → Type := fun i => Fin (twSz i) → BabyBear

/-- The radius schedule at `d = 0`: layers 0–4 = "not this layer's domain codeword", layer 5 =
"not a terminal residual" (degree `< 2` in `wchain 6 = omega16`), trivially `True` past the
schedule. -/
def farT : ∀ i, WT i → Prop
  | 0, w => w ∉ (towerS 0 (by omega)).C
  | 1, w => w ∉ (towerS 1 (by omega)).C
  | 2, w => w ∉ (towerS 2 (by omega)).C
  | 3, w => w ∉ (towerS 3 (by omega)).C
  | 4, w => w ∉ (towerS 4 (by omega)).C
  | 5, w => w ∉ rsCode (2 ^ 4) 2 (wchain 6)
  | _ + 6, _ => True

/-- The per-layer good sets: the graded `d = 0` sets of the tower layers. -/
noncomputable def goodT : ∀ i, WT i → Finset BabyBear := fun i w =>
  if h : i < 5 then goodδ (towerS i h) 0 w else ∅

/-- The per-layer fold: the tower layers' deployed arity-8 `Fold`; zero past the schedule. -/
noncomputable def foldT : ∀ i, WT i → BabyBear → WT (i + 1) := fun i w r =>
  if h : i < 5 then Fold (towerS i h).geom r w else fun _ => 0

private theorem step_mem (i : ℕ) (h : i < 5) (w : Fin (twSz i) → BabyBear) (r : BabyBear)
    (hr : r ∉ goodδ (towerS i h) 0 w) : Fold (towerS i h).geom r w ∉ (towerS i h).C' :=
  fun hmem => hr ((mem_goodδ _).mpr (closeN_zero_iff_mem.mpr hmem))

/-- **⚑ `ChainStepIdx` HOLDS AT THE TOWER — five real layers, the link load-bearing at each.**
Layers `0–3` step into the NEXT layer's domain-code complement THROUGH `tower_link`; layer 4
steps into the terminal residual complement. This is the multi-layer instance the L2 header
said could not yet exist. -/
theorem chainStepIdx_tower : ChainStepIdx farT goodT foldT := by
  intro i w r hfar hr
  match i with
  | 0 =>
      have h : (0 : ℕ) < 5 := by omega
      have h1 : (1 : ℕ) < 5 := by omega
      show foldT 0 w r ∉ (towerS 1 h1).C
      rw [← tower_link 0 h h1]
      simp only [foldT, dif_pos h]
      exact step_mem 0 h w r (by simpa only [goodT, dif_pos h] using hr)
  | 1 =>
      have h : (1 : ℕ) < 5 := by omega
      have h1 : (2 : ℕ) < 5 := by omega
      show foldT 1 w r ∉ (towerS 2 h1).C
      rw [← tower_link 1 h h1]
      simp only [foldT, dif_pos h]
      exact step_mem 1 h w r (by simpa only [goodT, dif_pos h] using hr)
  | 2 =>
      have h : (2 : ℕ) < 5 := by omega
      have h1 : (3 : ℕ) < 5 := by omega
      show foldT 2 w r ∉ (towerS 3 h1).C
      rw [← tower_link 2 h h1]
      simp only [foldT, dif_pos h]
      exact step_mem 2 h w r (by simpa only [goodT, dif_pos h] using hr)
  | 3 =>
      have h : (3 : ℕ) < 5 := by omega
      have h1 : (4 : ℕ) < 5 := by omega
      show foldT 3 w r ∉ (towerS 4 h1).C
      rw [← tower_link 3 h h1]
      simp only [foldT, dif_pos h]
      exact step_mem 3 h w r (by simpa only [goodT, dif_pos h] using hr)
  | 4 =>
      have h : (4 : ℕ) < 5 := by omega
      show foldT 4 w r ∉ rsCode (2 ^ 4) 2 (wchain 6)
      simp only [foldT, dif_pos h]
      exact step_mem 4 h w r (by simpa only [goodT, dif_pos h] using hr)
  | 5 => trivial
  | m + 6 => trivial

/-- The ROM query-point type: one slot per real layer (the deployed `enc` is a Merkle cap;
per-layer word injectivity is all the cover needs, and here it is literal). -/
abbrev QPt : Type := Option (Σ j : Fin 5, (Fin (twSz (j : ℕ)) → BabyBear))

/-- The transcript encoding: real layers map to their tagged word; the trivial tail
collapses. -/
def encT : (Σ i, WT i) → List BabyBear → QPt := fun w _ =>
  if h : w.1 < 5 then some ⟨⟨w.1, h⟩, w.2⟩ else none

open Classical in
/-- The bad-set cover: the graded good set at far words of real layers, empty elsewhere. -/
noncomputable def ET : QPt → Finset BabyBear := fun d =>
  match d with
  | none => ∅
  | some jw =>
      if jw.2 ∈ (towerS (jw.1 : ℕ) jw.1.isLt).C then ∅
      else goodδ (towerS (jw.1 : ℕ) jw.1.isLt) 0 jw.2

open Classical in
/-- The cover cap `b = 7 = n − 1`, from `goodδ_card_lt` (`FriChainStepIdx:460`) at every
layer — the PROVEN external cap, layer-uniform at fixed arity. -/
theorem ET_card_le : ∀ d, (ET d).card ≤ 7 := by
  intro d
  rcases d with _ | jw
  · exact Nat.zero_le 7
  · show (if jw.2 ∈ (towerS (jw.1 : ℕ) jw.1.isLt).C then (∅ : Finset BabyBear)
      else goodδ (towerS (jw.1 : ℕ) jw.1.isLt) 0 jw.2).card ≤ 7
    split_ifs with hf
    · simp
    · have hlt : (goodδ (towerS (jw.1 : ℕ) jw.1.isLt) 0 jw.2).card < 8 :=
        goodδ_card_lt _ (d := 0) (fun hcl => hf (closeN_zero_iff_mem.mp hcl))
      omega

open Classical in
/-- The far-conditional cover, discharged layer-by-layer. -/
theorem ET_cover : ∀ (i : ℕ) (w : WT i) (cs : List BabyBear),
    farT i w → goodT i w ⊆ ET (encT ⟨i, w⟩ cs) := by
  intro i w cs hfar
  by_cases h : i < 5
  · have hnot : w ∉ (towerS i h).C := by
      interval_cases i <;> exact hfar
    have hgood : goodT i w = goodδ (towerS i h) 0 w := dif_pos h
    have henc : encT ⟨i, w⟩ cs = some ⟨⟨i, h⟩, w⟩ := dif_pos h
    rw [hgood, henc]
    show goodδ (towerS i h) 0 w
        ⊆ (if w ∈ (towerS i h).C then (∅ : Finset BabyBear) else goodδ (towerS i h) 0 w)
    rw [if_neg hnot]
  · have hgood : goodT i w = ∅ := dif_neg h
    rw [hgood]
    exact Finset.empty_subset _

/-! ## §7 — ⚑ NON-VACUITY: the tower FIRES through all five deployed layers. -/

/-- The layer-0 far word: the degree-`2^16` monomial — the FIRST degree the deployed rate
excludes. PROVEN far by the DFT functional (`monoW_not_mem`), fully symbolically at the real
`2^19` domain. -/
noncomputable def farWord : Fin (twSz 0) → BabyBear := monoW (twSz 0) (2 ^ 16) (wchain 1)

theorem farWord_far : farT 0 farWord :=
  monoW_not_mem (wchain 1)
    (by rw [wchain_ord 1 (by norm_num)]; norm_num [twSz])
    (by norm_num) (by norm_num [twSz]) (by decide)

/-- Layer 1's farness is ALSO inhabited (the degree-`2^13` monomial): the layers are
individually non-degenerate — real far words at `≥ 2` layers, against the toy's one. -/
theorem layer1_far : farT 1 (monoW (twSz 1) (2 ^ 13) (wchain 2)) :=
  monoW_not_mem (wchain 2)
    (by rw [wchain_ord 2 (by norm_num)]; norm_num [twSz])
    (by norm_num) (by norm_num [twSz]) (by decide)

/-- The positive pole: an honest low-degree word folds INTO the weld at every challenge
(`fold_complete` at layer 0 — the completeness half the link preserves). -/
theorem tower_completeness_fires (h : (0 : ℕ) < 5) (α : BabyBear) :
    Fold (towerS 0 h).geom α (monoW (twSz 0) (2 ^ 3) (wchain 1)) ∈ (towerS 0 h).C' :=
  fold_complete (towerS 0 h) (monoW_mem (wchain 1) (by norm_num)) α

/-- The terminal of the 5-round FS chain sits at layer 5 (`terminal_layer`). -/
theorem tower_terminal_at_5 (H : QPt → BabyBear) :
    (honestStrategy (sigFold foldT) ⟨0, farWord⟩
        (fsChain encT (honestStrategy (sigFold foldT) ⟨0, farWord⟩) H 5 [])).1 = 5 :=
  terminal_layer foldT encT farWord H 5

open Classical in
/-- **⚑ THE TOWER FIRES — the composed survival bound over the FULL deployed schedule.** From
the proven-far `farWord` at the real `2^19` top domain, five FS rounds of the deployed arity-8
fold: any event implying "farness DIED somewhere across the five welded layers" (the terminal
layer-5 word is not far) has probability at most `5·7/|BabyBear| < 2^-25`. Every hypothesis of
`chain_far_survival_idx` is discharged concretely (`chainStepIdx_tower`, `ET_card_le`,
`ET_cover`, `farWord_far`) — the L2 machinery genuinely runs at the multi-layer deployed shape
it was built for, which `FriChainStepIdx` §6 could do at ONE layer only. -/
theorem tower_chain_far_survival :
    winProb (fun H : QPt → BabyBear =>
        decide (¬ sigFar farT (honestStrategy (sigFold foldT) ⟨0, farWord⟩
          (fsChain encT (honestStrategy (sigFold foldT) ⟨0, farWord⟩) H 5 []))))
      ≤ (35 : ℝ) / (Fintype.card BabyBear : ℝ) := by
  refine le_trans
    (chain_far_survival_idx (W := WT) chainStepIdx_tower encT ET ET_card_le farWord ET_cover
      farWord_far 5 ?_)
    (le_of_eq (by norm_num))
  intro H hH
  exact of_decide_eq_true hH

/-- The fired bound is genuinely nontrivial: `35/|BabyBear| < 1` (indeed `< 2^-25`). -/
theorem tower_bound_lt_one : (35 : ℝ) / (Fintype.card BabyBear : ℝ) < 1 := by
  rw [ZMod.card]
  norm_num

/-! ## §8 — the TAMPER CANARIES: a mis-linked tower is REJECTED, from both sides.

Layer 0's true folded code is `rsCode (2^16) (2^13) (wchain 2)`. We tamper the DEGREE both
ways (the "wrong degree at a layer" mis-weld; a wrong DOMAIN SIZE cannot even be stated — the
types reject it) and show each tamper is refuted, so the link is load-bearing content. -/

/-- **CANARY (link equation)** — halve layer 1's code degree (`2^12` for `2^13`: the mis-weld
"degree divides by 16, not by the fold arity 8") and the link EQUATION itself refutes it: the
degree-`2^12` monomial separates `(towerS 0).C'` from the tampered code. -/
theorem canary_halved_degree_link (h0 : (0 : ℕ) < 5) :
    (towerS 0 h0).C' ≠ rsCode (2 ^ 16) (2 ^ 12) (wchain 2) := by
  intro heq
  have hmem : monoW (2 ^ 16) (2 ^ 12) (wchain 2) ∈ (towerS 0 h0).C' :=
    monoW_mem (wchain 2) (by norm_num)
  rw [heq] at hmem
  exact monoW_not_mem (wchain 2)
    (by rw [wchain_ord 2 (by norm_num)])
    le_rfl (by norm_num) (by decide) hmem

/-- **CANARY (too small is UNBUILDABLE)** — a tower whose layer-0 `C'` is the halved-degree
code cannot even be CONSTRUCTED: the `foldC_mem` closure obligation is FALSE for it. Witness:
the degree-`8·2^12` domain codeword whose 0-component is the degree-`2^12` monomial, outside
the tampered code. -/
theorem canary_halved_degree_unbuildable (h0 : (0 : ℕ) < 5) :
    ¬ ∀ f ∈ (towerS 0 h0).C, ∀ j : Fin 8,
        Cj (towerS 0 h0).geom j f ∈ rsCode (2 ^ 16) (2 ^ 12) (wchain 2) := by
  intro hall
  have h08 : (0 : ℕ) < 8 := by norm_num
  have hfmem : monoW (twSz 0) (8 * 2 ^ 12) (wchain 1) ∈ (towerS 0 h0).C :=
    monoW_mem (wchain 1) (by norm_num)
  have hCj := hall _ hfmem (⟨0, h08⟩ : Fin 8)
  have heq : Cj (towerS 0 h0).geom (⟨0, h08⟩ : Fin 8) (monoW (twSz 0) (8 * 2 ^ 12) (wchain 1))
      = monoW (2 ^ 16) (2 ^ 12) (wchain 2) :=
    Cj_monoW 8 (2 ^ 16) h08 (by norm_num) (wchain 1)
      (by rw [wchain_ord 1 (by norm_num)]; norm_num) (2 ^ 12)
  rw [heq] at hCj
  exact monoW_not_mem (wchain 2)
    (by rw [wchain_ord 2 (by norm_num)])
    le_rfl (by norm_num) (by decide) hCj

/-- **CANARY (too big is UNBUILDABLE)** — inflate layer-0's `C'` by ONE degree and the
`unfold_closed` closure obligation is FALSE: reassembling the now-admitted degree-`2^13`
monomial produces the degree-`2^16` monomial — LITERALLY `farWord`, the proven non-codeword.
The weld pins `C'` exactly; a mis-linked tower manufactures far words and calls them
codewords. -/
theorem canary_inflated_degree_unbuildable (h0 : (0 : ℕ) < 5) :
    ¬ ∀ Df : Fin 8 → (Fin (2 ^ 16) → BabyBear),
        (∀ a, Df a ∈ rsCode (2 ^ 16) (2 ^ 13 + 1) (wchain 2)) →
        reassemble (towerS 0 h0).geom Df ∈ (towerS 0 h0).C := by
  intro hall
  have h08 : (0 : ℕ) < 8 := by norm_num
  have hDf : ∀ a : Fin 8,
      (fun a' => if a' = (⟨0, h08⟩ : Fin 8) then monoW (2 ^ 16) (2 ^ 13) (wchain 2) else 0) a
        ∈ rsCode (2 ^ 16) (2 ^ 13 + 1) (wchain 2) := by
    intro a
    by_cases ha : a = (⟨0, h08⟩ : Fin 8)
    · show (if a = (⟨0, h08⟩ : Fin 8) then monoW (2 ^ 16) (2 ^ 13) (wchain 2) else 0) ∈ _
      rw [if_pos ha]
      exact monoW_mem (wchain 2) (by norm_num)
    · show (if a = (⟨0, h08⟩ : Fin 8) then monoW (2 ^ 16) (2 ^ 13) (wchain 2) else 0) ∈ _
      rw [if_neg ha]
      exact Submodule.zero_mem _
  have hmem := hall _ hDf
  have heq : reassemble (towerS 0 h0).geom
      (fun a' => if a' = (⟨0, h08⟩ : Fin 8) then monoW (2 ^ 16) (2 ^ 13) (wchain 2) else 0)
      = monoW (twSz 0) (8 * 2 ^ 13) (wchain 1) :=
    reassemble_single_mono 8 (2 ^ 16) h08 (by norm_num) (wchain 1)
      (by rw [wchain_ord 1 (by norm_num)]; norm_num) (2 ^ 13)
  have hfar : monoW (twSz 0) (8 * 2 ^ 13) (wchain 1) ∉ (towerS 0 h0).C :=
    monoW_not_mem (wchain 1)
      (by rw [wchain_ord 1 (by norm_num)]; norm_num [twSz])
      (by norm_num) (by norm_num [twSz]) (by decide)
  refine hfar ?_
  rw [← heq]
  exact hmem

/-! ## §9 — kernel-clean keystones. -/

#assert_all_clean [
  pow_inj_of_orderOf,
  monoW_mem,
  monoW_not_mem,
  Cj_reassemble,
  reassemble_tower,
  w22_ord,
  wchain_ord,
  wchain_six,
  tower_link,
  tower_bottom_is_omega16_code,
  chainStepIdx_tower,
  ET_card_le,
  ET_cover,
  farWord_far,
  layer1_far,
  tower_completeness_fires,
  tower_terminal_at_5,
  tower_chain_far_survival,
  tower_bound_lt_one,
  canary_halved_degree_link,
  canary_halved_degree_unbuildable,
  canary_inflated_degree_unbuildable
]

end Dregg2.Circuit.FriSetupTower
