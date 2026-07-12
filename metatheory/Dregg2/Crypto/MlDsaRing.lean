/-
# `Dregg2.Crypto.MlDsaRing` — the REAL ML-DSA-65 polynomial ring `R_q = ℤ_q[X]/(X²⁵⁶+1)`, as EXECUTABLE `def`s.

FIPS 204. `q = 8380417`, `n = 256`. This module builds the negacyclic ring arithmetic and the ML-DSA
number-theoretic transform as plain computable `def`s (the same `leanc`-extractable shape as
`Dregg2.Crypto.Keccak` — BRICK 1, already byte-exact): no `Prop`, no classical choice, only `Nat`/`Array`
arithmetic reduced mod `q` with canonical reps in `[0, q)`.

It is BRICK 2 of replacing the `A = id` scalar caricature in `Fips204Verify.lean` with the real ML-DSA-65
verify. Every ML-DSA object — `SampleInBall`, `ExpandA`, the `t`/`z`/`w` vectors, the `A·z` matrix product —
lives in this ring, and the fast path multiplies polynomials in the NTT domain. So the correctness of the
whole verify rests on THIS module's `ntt`/`intt` being an honest length-256 negacyclic transform: the fast
`intt (pointwiseMul (ntt a) (ntt b))` must equal the ground-truth `schoolbookMul a b` (the real
`(a·b) mod (X²⁵⁶+1)` product, with the `X²⁵⁶ = −1` sign on wraparound).

## THE ANTI-FAKE GATE (checked, not asserted)

Executable `native_decide` theorems over CONCRETE polynomials pin the transform:

* `ntt_intt_id` — `intt (ntt a) = a` (round-trip; the inverse is a true inverse).
* `ntt_computes_negacyclic_mul` — `intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b`, on a pair with
  genuine high-degree wraparound (so the `X²⁵⁶ = −1` sign is exercised). THE load-bearing gate: the fast
  transform equals the real negacyclic ring product.
* `zeta_primitive_512th_root` — `ζ²⁵⁶ ≡ −1 (mod q)` for `ζ = 1753` (the property that makes the negacyclic
  NTT well-defined at all).
* `mul_mod_q_sanity` — `(q−1)·(q−1) ≡ 1 (mod q)` (reduction sanity).

`native_decide` runs the COMPILED `def`s. If the ζ-power order (FIPS 204 Algorithm 41 uses `ζ^{brv(k)}`, the
8-bit-reversed exponent), the bit-reversal, or the `intt` scaling (`256⁻¹ mod q = 8347681`) were wrong, these
theorems would NOT close. No `sorry`, no user `axiom`, no toy substitute for the transform.

## RESIDUAL

The gate theorems use `native_decide`, whose trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` (the
compiled-evaluation residual — the SAME class `Keccak` and `Fips204Verify` already name for their extracted
cores).
-/

namespace Dregg2.Crypto.MlDsaRing

/-! ## `ℤ_q` scalar arithmetic (`q = 8380417`, canonical reps in `[0, q)`) -/

/-- The ML-DSA modulus, FIPS 204 Table 1: `q = 2²³ − 2¹³ + 1 = 8380417`. -/
def q : Nat := 8380417

/-- Modular add of two canonical reps in `[0, q)`. -/
@[inline] def addQ (a b : Nat) : Nat := (a + b) % q

/-- Modular subtract of two canonical reps in `[0, q)` (`a − b mod q`, kept nonnegative). -/
@[inline] def subQ (a b : Nat) : Nat := (a + q - b) % q

/-- Modular multiply, reducing the full product mod `q`. -/
@[inline] def mulModQ (a b : Nat) : Nat := (a * b) % q

/-- Modular exponentiation by square-and-multiply. Exponents used here are `< 512`, so a fixed 32-bit ladder
covers them (once the exponent is exhausted the remaining squarings are harmless no-ops on `result`). -/
def powModQ (base e : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := base % q
  let mut ex := e
  for _ in [0:32] do
    if ex % 2 == 1 then result := mulModQ result b
    b := mulModQ b b
    ex := ex / 2
  return result

/-! ## The negacyclic ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` -/

/-- A polynomial in `R_q`: 256 coefficients, each a canonical `ℤ_q` rep in `[0, q)`, coefficient `i` = the
`Xⁱ` term. -/
abbrev Poly := Array Nat

/-- The zero polynomial. -/
def zeroPoly : Poly := Array.replicate 256 0

/-- Set coefficient `i` to `v` (reduced mod `q`). Convenience for building concrete test polynomials. -/
def setC (p : Poly) (i v : Nat) : Poly := p.set! i (v % q)

/-- Coefficient-wise sum in `R_q`. -/
def addPoly (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (addQ a[i]! b[i]!)
  return c

/-- Coefficient-wise difference in `R_q`. -/
def subPoly (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (subQ a[i]! b[i]!)
  return c

/-- **The ground-truth negacyclic product** `(a·b) mod (X²⁵⁶+1)` in `R_q`. Schoolbook convolution with the
`X²⁵⁶ = −1` wrap: `c_k = Σ_{i+j=k} a_i b_j − Σ_{i+j=k+256} a_i b_j`, all mod `q`. This is the reference the
fast NTT path is checked against. -/
def schoolbookMul (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    for j in [0:256] do
      let prod := mulModQ a[i]! b[j]!
      let k := i + j
      if k < 256 then
        c := c.set! k (addQ c[k]! prod)          -- Xⁱ⁺ʲ, no wrap
      else
        c := c.set! (k - 256) (subQ c[k - 256]! prod)   -- X²⁵⁶ = −1 : subtract
  return c

/-! ## The ML-DSA number-theoretic transform (FIPS 204 §7.5, Algorithms 41 & 42)

`q = 8380417` admits a primitive 512th root of unity `ζ = 1753`. The forward NTT (Algorithm 41) is a
length-256 negacyclic Cooley–Tukey transform whose twiddle at step `k` is `ζ^{brv(k)}`, where `brv` reverses
the low 8 bits of `k`. The inverse (Algorithm 42) is the Gentleman–Sande dual with twiddle `−ζ^{brv(k)}`
followed by scaling every coefficient by `256⁻¹ mod q = 8347681`. -/

/-- ML-DSA's primitive 512th root of unity mod `q`, FIPS 204. -/
def zeta : Nat := 1753

/-- `256⁻¹ mod q`, FIPS 204 (the `intt` final scaling). -/
def nInv : Nat := 8347681

/-- Reverse the low 8 bits of `k` (FIPS 204's `brv`). -/
def brv8 (k : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := k
  for _ in [0:8] do
    r := r * 2 + x % 2
    x := x / 2
  return r

/-- The FIPS 204 twiddle at step `k`: `ζ^{brv(k)} mod q`. -/
def zetaTwiddle (k : Nat) : Nat := powModQ zeta (brv8 k)

/-- **Forward NTT** (FIPS 204 Algorithm 41). Eight Cooley–Tukey stages, `len = 128, 64, …, 1`; at stage `s`
there are `128/len` butterfly blocks, each consuming the next twiddle `k = 1 … 255` in order. -/
def ntt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut k := 0
  for s in [0:8] do
    let len := 128 >>> s              -- 128, 64, …, 1
    let nblk := 128 / len             -- 256 / (2·len) = number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k + 1
      let z := zetaTwiddle k
      for j in [start : start + len] do
        let t := mulModQ z a[j + len]!
        a := a.set! (j + len) (subQ a[j]! t)
        a := a.set! j (addQ a[j]! t)
  return a

/-- **Inverse NTT** (FIPS 204 Algorithm 42). Gentleman–Sande dual: eight stages `len = 1, 2, …, 128`, twiddle
`−ζ^{brv(k)}` with `k` counting down `255 … 1`, then scale every coefficient by `256⁻¹ mod q`. -/
def intt (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut k := 256
  for s in [0:8] do
    let len := 1 <<< s                -- 1, 2, …, 128
    let nblk := 128 / len             -- number of blocks this stage
    for blk in [0:nblk] do
      let start := blk * 2 * len
      k := k - 1
      let z := subQ 0 (zetaTwiddle k)  -- −ζ^{brv(k)} mod q
      for j in [start : start + len] do
        let t := a[j]!
        a := a.set! j (addQ t a[j + len]!)
        a := a.set! (j + len) (mulModQ z (subQ t a[j + len]!))
  for j in [0:256] do
    a := a.set! j (mulModQ nInv a[j]!)   -- scale by 256⁻¹ mod q
  return a

/-- Coefficient-wise product in the NTT domain (the fast negacyclic multiply combines with `ntt`/`intt`). -/
def pointwiseMul (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := c.set! i (mulModQ a[i]! b[i]!)
  return c

/-! ## THE ANTI-FAKE GATE — `native_decide` over concrete polynomials.

If the ζ-power order, the bit-reversal, or the `intt` scaling were wrong, these would NOT close. -/

/-- A concrete nonzero test poly with a high-degree term: `a = 1 + 2·X + 7·X²⁵⁵`. -/
def sampleA : Poly := setC (setC (setC zeroPoly 0 1) 1 2) 255 7

/-- A second concrete test poly with high-degree terms: `b = 4 + 5·X¹⁰⁰ + 6·X²⁰⁰`. -/
def sampleB : Poly := setC (setC (setC zeroPoly 0 4) 100 5) 200 6

/-- **Reduction sanity**: `(q−1)·(q−1) ≡ 1 (mod q)`. Kernel `decide` (no loop; pure `Nat` `*`/`%`),
so this carries NO `Lean.ofReduceBool`/`trustCompiler` — axiom set ⊆ {propext, Classical.choice, Quot.sound}. -/
theorem mul_mod_q_sanity : mulModQ (q - 1) (q - 1) = 1 := by decide

/-- **`ζ` is a primitive 512th root**: `ζ²⁵⁶ ≡ −1 (mod q)`. The property that makes the negacyclic NTT
well-defined; if `ζ = 1753` or `q` were wrong this fails.
`native_decide` (genuine limit): `powModQ` is a `for _ in [0:32]` loop; `Std.Range.forIn` uses well-founded
recursion that does NOT reduce under the kernel, so `decide` gets stuck. (The field-cast form `ζ^256 = -1` in
`ZMod q` — `NttFaithful.zeta_root_witness` — IS kernel-`decide`-clean.) -/
theorem zeta_primitive_512th_root : powModQ zeta 256 = q - 1 := by native_decide

/-- **Round-trip**: `intt (ntt a) = a` on a concrete nonzero poly. The inverse transform is a true inverse
(correct twiddle order AND `256⁻¹` scaling). -/
theorem ntt_intt_id : intt (ntt sampleA) = sampleA := by native_decide

/-- **THE load-bearing gate**: the fast NTT path equals the ground-truth negacyclic ring product,
`intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b`. The chosen `a, b` have high-degree terms
(`X²⁵⁵ · X²⁰⁰` lands at `X⁴⁵⁵ = −X¹⁹⁹`), so the `X²⁵⁶ = −1` sign is genuinely exercised. -/
theorem ntt_computes_negacyclic_mul :
    intt (pointwiseMul (ntt sampleA) (ntt sampleB)) = schoolbookMul sampleA sampleB := by native_decide

end Dregg2.Crypto.MlDsaRing
