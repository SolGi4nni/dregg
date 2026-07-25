/-
# Dregg2.Crypto.BN254.Primality — the machine-checked discharge of `BN254BasePrimeGoal`.

The base-field primality seam named (not axiomatized) in `Fq.lean` is CLOSED here: `pBN254` is
proven prime by a genuine **recursive Pratt / Lucas certificate**, kernel-checked, with NO `sorry`,
NO `axiom`, and NO `native_decide` (the banned unverified-compiler path).  Discharging it upgrades
`Fq = ZMod pBN254` to a real `Field` (Mathlib's `[Fact p.Prime]`-gated instance now fires
unconditionally) and ripples into the tower and the curve point groups.

## The certificate machinery (self-contained, House Law #1: the math is authored in Lean).

`norm_num`'s primality extension tops out near 25 bits; `pBN254` is 254 bits.  The Lucas test
(`Mathlib.NumberTheory.LucasPrimality.lucas_primality`) certifies `n` prime from a witness `g` with
`g^(n-1) = 1` and `g^((n-1)/q) ≠ 1` for every prime `q ∣ n-1`.  The two obstacles are (1) evaluating
a 254-bit modular exponentiation inside the KERNEL — Mathlib's `Monoid.npow` on `ZMod n` is
`npowRec` (LINEAR in the exponent ⇒ `2^254` steps, intractable) — and (2) enumerating the prime
divisors of `n-1`, which recurses into sub-certificates for each large factor.

* `powModFuel n g fuel e` — square-and-multiply `g^e % n` as a FUEL-indexed **structural** recursion
  (`Nat.rec` on `fuel`, so the kernel reduces it in `O(fuel)` steps, each a GMP-accelerated `Nat`
  mul/mod on ≤ `2·bits(n)` numbers — NOT `2^bits` steps).  `powModFuel_correct` proves it equals
  `g^e % n` by a one-time induction (no big computation).  `decide` then reduces the concrete
  254-bit fold to a literal and the kernel checks it — a REAL kernel proof, not `native_decide`.
* `zmod_pow_{eq,ne}_one_of_powModFuel` bridge the `Nat` computation to `(g : ZMod n)^e`.
* `prodPow` / `prime_dvd_prodPow` / `lucasList` package the Lucas test: given the factorization
  `n-1 = ∏ qᵢ^{eᵢ}` (each `qᵢ` prime), a prime `q ∣ n-1` must be one of the `qᵢ`, so the finite
  per-factor `g^((n-1)/qᵢ) ≠ 1` checks (each a `powModFuel` `decide`) suffice.

## The factorization (CORRECTED).

`pBN254 - 1 = 2 · 3² · 13 · 29 · 67 · 229 · 311 · 983 · 11003 · 405928799 · 11465965001 ·
13427688667394608761327070753331941386769` (primitive root `g = 3`).  Note `pBN254` has 2-adicity
**1** (`p ≡ 3 mod 4`), NOT 28 — the high-2-adicity `2^28·…` factorization belongs to the *scalar*
field `r-1`, a common conflation.  Eight of the distinct prime factors across the recursion are
large enough to need their own Lucas sub-certificate; they are proven below in dependency order
(leaves first), each `#print axioms`-clean.
-/
import Dregg2.Crypto.BN254.Fq
import Dregg2.Crypto.BN254.Fp2
import Dregg2.Crypto.BN254.Curves
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
-- The 254-bit `powModFuel` folds recurse ~254 levels; the kernel `decide` needs the headroom.
set_option maxRecDepth 8000

namespace Dregg2.Crypto.BN254.Primality

/-! ## §1 Fuel-indexed modular exponentiation and its correctness. -/

/-- Square-and-multiply `g^e % n`, as a FUEL-structural recursion so the kernel reduces it in
`O(fuel)` GMP-accelerated `Nat` steps (vs. `npowRec`'s `O(e)`).  Base returns `1 % n`. -/
def powModFuel (n g : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % n
  | fuel+1, e =>
      if e = 0 then 1 % n
      else
        let half := powModFuel n g fuel (e / 2)
        let sq := (half * half) % n
        if e % 2 = 1 then (sq * g) % n else sq

/-- `powModFuel` computes `g^e % n` whenever the fuel covers the exponent (`e < 2^fuel`). Proven by
induction on `fuel` — a one-time proof, no large computation. -/
theorem powModFuel_correct (n g : ℕ) :
    ∀ (fuel e : ℕ), e < 2 ^ fuel → powModFuel n g fuel e = g ^ e % n := by
  intro fuel
  induction fuel with
  | zero => intro e he; simp only [pow_zero, Nat.lt_one_iff] at he; subst he; simp [powModFuel]
  | succ fuel ih =>
      intro e he
      unfold powModFuel
      by_cases h0 : e = 0
      · subst h0; simp
      · rw [if_neg h0, ih (e / 2) (by
          have : e < 2 ^ fuel * 2 := by rw [← pow_succ]; exact he
          omega)]
        have hsq : g ^ (e / 2) % n * (g ^ (e / 2) % n) % n = g ^ (2 * (e / 2)) % n := by
          rw [← Nat.mul_mod, ← pow_add]; congr 2; omega
        by_cases hpar : e % 2 = 1
        · rw [if_pos hpar, hsq, Nat.mod_mul_mod, ← pow_succ]; congr 2; omega
        · rw [if_neg hpar, hsq]; congr 2; omega

/-- Bridge: a `powModFuel … (n-1) = 1` computation forces `(g : ZMod n)^(n-1) = 1`. -/
theorem zmod_pow_eq_one_of_powModFuel {n g fuel : ℕ}
    (hn1 : 1 < n) (hfuel : n - 1 < 2 ^ fuel)
    (h : powModFuel n g fuel (n - 1) = 1) : (g : ZMod n) ^ (n - 1) = 1 := by
  have hmod : g ^ (n - 1) % n = 1 := (powModFuel_correct n g fuel (n - 1) hfuel) ▸ h
  have hme : (g ^ (n - 1) : ℕ) ≡ 1 [MOD n] := by
    unfold Nat.ModEq; rw [hmod, Nat.mod_eq_of_lt hn1]
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hme
  push_cast at this; exact this

/-- Bridge: a `powModFuel … e ≠ 1` computation forces `(g : ZMod n)^e ≠ 1`. -/
theorem zmod_pow_ne_one_of_powModFuel {n g fuel e : ℕ}
    (hn1 : 1 < n) (hfuel : e < 2 ^ fuel)
    (h : powModFuel n g fuel e ≠ 1) : (g : ZMod n) ^ e ≠ 1 := by
  intro hcontra; apply h
  rw [powModFuel_correct n g fuel e hfuel]
  have hcast : ((g ^ e : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; exact hcontra
  have hme := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  unfold Nat.ModEq at hme; rw [hme, Nat.mod_eq_of_lt hn1]

/-! ## §2 Packaging the Lucas test over an explicit factorization. -/

/-- `∏ (q,e) in pf, q^e`. -/
def prodPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (q, e) :: rest => q ^ e * prodPow rest

/-- A prime dividing `∏ qᵢ^{eᵢ}` (each `qᵢ` prime) equals one of the `qᵢ`. -/
theorem prime_dvd_prodPow {q : ℕ} (hq : q.Prime) :
    ∀ (pf : List (ℕ × ℕ)), q ∣ prodPow pf → (∀ qe ∈ pf, Nat.Prime qe.1) →
    ∃ qe ∈ pf, q = qe.1 := by
  intro pf
  induction pf with
  | nil => intro hdvd _; simp only [prodPow, Nat.dvd_one] at hdvd; exact absurd hdvd hq.ne_one
  | cons head rest ih =>
      intro hdvd hprime
      rw [prodPow] at hdvd
      rcases (hq.dvd_mul).mp hdvd with hl | hr
      · have hph : Nat.Prime head.1 := hprime head (by simp)
        have hqh : q = head.1 := (Nat.prime_dvd_prime_iff_eq hq hph).mp (hq.dvd_of_dvd_pow hl)
        exact ⟨head, by simp, hqh⟩
      · obtain ⟨qe, hmem, heq⟩ := ih hr (fun x hx => hprime x (by simp [hx]))
        exact ⟨qe, by simp [hmem], heq⟩

/-- **The Lucas-certificate combinator.** From a factorization of `n-1` into (proven-prime) factors,
a witness `g`, and the finite `powModFuel` checks, conclude `n` is prime — via Mathlib's
`lucas_primality`.  Every hypothesis is discharged by `decide` / `norm_num` at each use site. -/
theorem lucasList (n g fuel : ℕ) (pf : List (ℕ × ℕ))
    (hn1 : 1 < n) (hfuel : n - 1 < 2 ^ fuel)
    (hprod : n - 1 = prodPow pf)
    (hprime : ∀ qe ∈ pf, Nat.Prime qe.1)
    (h1 : powModFuel n g fuel (n - 1) = 1)
    (hd : ∀ qe ∈ pf, powModFuel n g fuel ((n - 1) / qe.1) ≠ 1) : Nat.Prime n := by
  apply lucas_primality n (g : ZMod n)
  · exact zmod_pow_eq_one_of_powModFuel hn1 hfuel h1
  · intro q hq hqdvd
    rw [hprod] at hqdvd
    obtain ⟨qe, hmem, rfl⟩ := prime_dvd_prodPow hq pf hqdvd hprime
    exact zmod_pow_ne_one_of_powModFuel hn1
      (lt_of_le_of_lt (Nat.div_le_self _ _) hfuel) (hd qe hmem)

/-! ## §3 The recursive certificate for `pBN254` (leaves first, each axiom-clean). -/

theorem prime_327599 : Nat.Prime 327599 :=
  lucasList 327599 19 19 [(2, 1), (19, 1), (37, 1), (233, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_1853641 : Nat.Prime 1853641 :=
  lucasList 1853641 17 21 [(2, 3), (3, 2), (5, 1), (19, 1), (271, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_4562087 : Nat.Prime 4562087 :=
  lucasList 4562087 5 23 [(2, 1), (17, 1), (109, 1), (1231, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_173171039 : Nat.Prime 173171039 :=
  lucasList 173171039 13 28 [(2, 1), (73, 1), (89, 1), (13327, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_405928799 : Nat.Prime 405928799 :=
  lucasList 405928799 22 29 [(2, 1), (11, 1), (3691, 1), (4999, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_1263766531 : Nat.Prime 1263766531 :=
  lucasList 1263766531 10 31 [(2, 1), (3, 1), (5, 1), (13, 1), (911, 1), (3557, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_11465965001 : Nat.Prime 11465965001 :=
  lucasList 11465965001 3 34 [(2, 3), (5, 4), (7, 1), (327599, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_327599 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_35385462869 : Nat.Prime 35385462869 :=
  lucasList 35385462869 2 36 [(2, 2), (7, 1), (1263766531, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_1263766531 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_2480874801745591 : Nat.Prime 2480874801745591 :=
  lucasList 2480874801745591 6 52 [(2, 1), (3, 2), (5, 1), (19, 1), (41, 1), (35385462869, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_35385462869 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_13427688667394608761327070753331941386769 : Nat.Prime 13427688667394608761327070753331941386769 :=
  lucasList 13427688667394608761327070753331941386769 17 134 [(2, 4), (3, 1), (7, 1), (11, 1), (1853641, 1), (4562087, 1), (173171039, 1), (2480874801745591, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_1853641 | exact prime_4562087 | exact prime_173171039 | exact prime_2480874801745591 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_21888242871839275222246405745257275088696311157297823662689037894645226208583 : Nat.Prime 21888242871839275222246405745257275088696311157297823662689037894645226208583 :=
  lucasList 21888242871839275222246405745257275088696311157297823662689037894645226208583 3 254 [(2, 1), (3, 2), (13, 1), (29, 1), (67, 1), (229, 1), (311, 1), (983, 1), (11003, 1), (405928799, 1), (11465965001, 1), (13427688667394608761327070753331941386769, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_405928799 | exact prime_11465965001 | exact prime_13427688667394608761327070753331941386769 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

/-! ## §4 The crown: `Nat.Prime pBN254` and the `Fact` instance. -/

/-- **`pBN254` is prime** — the discharge of `BN254BasePrimeGoal`, machine-checked. -/
theorem prime_pBN254 : Nat.Prime Dregg2.Crypto.BN254.pBN254 := prime_21888242871839275222246405745257275088696311157297823662689037894645226208583

end Dregg2.Crypto.BN254.Primality

namespace Dregg2.Crypto.BN254

open Primality

/-- **`BN254BasePrimeGoal` is DISCHARGED** — the named base-field primality seam from `Fq.lean`,
now a theorem (recursive Pratt/Lucas certificate; no `sorry`/`axiom`/`native_decide`). -/
theorem bn254BasePrimeGoal_holds : BN254BasePrimeGoal := prime_pBN254

/-- The `Fact` instance the whole downstream field tower and both curve point groups consume.  With
it in scope, Mathlib's `[Fact p.Prime]`-gated instances fire UNCONDITIONALLY. -/
instance : Fact (Nat.Prime pBN254) := ⟨prime_pBN254⟩

/-! ## §5 The ripple — the conditional field/group structures are now unconditional. -/

/-- `Fq = ZMod pBN254` is a genuine `Field` (was `example [Fact …]` in `Fq.lean`); Mathlib's
`[Fact p.Prime]`-gated `ZMod.instField` now resolves.  (An `example`, not a fresh instance, to
avoid a competing `Field Fq` diamond — the canonical instance is Mathlib's.) -/
noncomputable example : Field Fq := inferInstance

/-- The G1 point group is an `AddCommGroup` unconditionally (was `example [Fact …]` in `Curves.lean`). -/
noncomputable example : AddCommGroup G1Point := inferInstance

/-- `-1` is not a square in `Fq` (`p ≡ 3 mod 4`) — the non-residue fact the `Fp2` field-ness rides. -/
theorem fq_neg_one_not_isSquare : ¬ IsSquare (-1 : Fq) := by
  intro h; rw [ZMod.exists_sq_eq_neg_one_iff] at h; exact h (by decide)

open Fp2 in
/-- **`Fp2FieldGoal` is DISCHARGED**: `X²+1` is irreducible over `Fq`, i.e. the `Fp2` norm
`c0²+c1²` vanishes only at `0`.  Follows from `Fq` being a field with `-1` a non-residue. -/
theorem fp2FieldGoal_holds : Fp2FieldGoal := by
  intro a ha hnorm
  apply ha
  have h0 : a.c0 * a.c0 + a.c1 * a.c1 = 0 := hnorm
  have hc1 : a.c1 = 0 := by
    by_contra hne
    apply fq_neg_one_not_isSquare
    refine ⟨a.c0 * a.c1⁻¹, ?_⟩
    have hi : a.c1 * a.c1⁻¹ = 1 := mul_inv_cancel₀ hne
    have hsq : a.c0 * a.c0 = -(a.c1 * a.c1) := by linear_combination h0
    have e1 : a.c0 * a.c1⁻¹ * (a.c0 * a.c1⁻¹) = a.c0 * a.c0 * (a.c1⁻¹ * a.c1⁻¹) := by ring
    rw [e1, hsq]
    have e2 : -(a.c1 * a.c1) * (a.c1⁻¹ * a.c1⁻¹) = -((a.c1 * a.c1⁻¹) * (a.c1 * a.c1⁻¹)) := by ring
    rw [e2, hi]; ring
  have hc0 : a.c0 = 0 := by
    have : a.c0 * a.c0 = 0 := by rw [hc1] at h0; simpa using h0
    exact mul_self_eq_zero.mp this
  ext <;> simp [hc0, hc1]

/-- `ofFq` is multiplicative — the base embedding lands the inverse formula in `Fp2`. -/
theorem ofFq_mul (x y : Fq) : Fp2.ofFq x * Fp2.ofFq y = Fp2.ofFq (x * y) := by
  ext <;> simp [Fp2.ofFq]

open Fp2 in
/-- **`Fp2` is a genuine field.**  With `Fp2FieldGoal` discharged the norm is invertible off `0`, so
`a⁻¹ = conj a · (normFp2 a)⁻¹` inverts (`a · conj a = normFp2 a`); packaged as `IsField Fp2`. -/
theorem fp2_isField : IsField Fp2 where
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (α := Fq) (by simpa using congrArg Fp2.c0 h)⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro a ha
    have hn : normFp2 a ≠ 0 := fp2FieldGoal_holds a ha
    refine ⟨conj a * ofFq ((normFp2 a)⁻¹), ?_⟩
    rw [← mul_assoc, mul_conj, ofFq_mul, mul_inv_cancel₀ hn]; rfl

/-- The `Field Fp2` instance (from `fp2_isField`).  `Fp2` was a bare coordinate `CommRing`; this is
the FIRST tower level made an actual field, so `X²+1` irreducibility is realized, not just named. -/
noncomputable instance : Field Fp2 := fp2_isField.toField

/-- The G2 point group is now an `AddCommGroup` unconditionally too — it consumed `Field Fp2`. -/
noncomputable example : AddCommGroup G2Point := inferInstance

#assert_axioms prime_pBN254
#assert_axioms bn254BasePrimeGoal_holds
#assert_axioms fp2FieldGoal_holds
#assert_axioms fp2_isField

end Dregg2.Crypto.BN254
