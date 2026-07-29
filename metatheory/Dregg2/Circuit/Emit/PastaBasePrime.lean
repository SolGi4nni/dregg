/-
# Dregg2.Circuit.Emit.PastaBasePrime — `Nat.Prime pN`, machine-checked: the Pallas base modulus.

## Why this file exists

Four sibling files in this tree name the SAME missing ingredient: `KimchiVerify.lean`,
`KimchiRealProofGate.lean`, `PicklesRecursion.lean` and `PastaIpaDeferral.lean` each say, in
their own words, that there is **no `Field (ZMod pN)` instance in the tree** — no in-kernel
primality proof of the 255-bit Pallas base modulus — and route around needing one. That
avoidance is exactly right for those files' own goals. It is NOT an option for the RCB-transport
work in `PastaGroupLaw.lean`: Mathlib's `WeierstrassCurve.Projective.Point.instAddCommGroup` (the
formal Pallas group law, with a REAL proved `add_assoc`) is stated for `{W : Projective F}
[Field F]`, full stop. Without `Field (ZMod pN)` there is no group law to transport into.

## The certificate (computed outside Lean, checked inside — this tree's own precedent)

`Dregg2.Crypto.BN254.Primality` already built a GENERIC recursive Pratt/Lucas certificate
combinator (`powModFuel`, `powModFuel_correct`, `lucasList`) to discharge `Nat.Prime pBN254` (254
bits) without `native_decide`. It is reused here verbatim — it is not BN254-specific despite its
address; only that file's LATER sections (the `Fp2`/pairing ripple) are. Reusing it here, instead
of re-deriving the same fuel-indexed-modexp machinery a second time, is the same call this tree
already made when `RomForkingExtractor` reused `manyFreshDistinct_bound` across the IPA/FRI seam.

`pN − 1 = 2³² · 3 · 463 · a · b`, where
  `a = 539204044132271846773` (69 bits) and
  `b = 8999194758858563409123804352480028797519453` (143 bits),
fully factored by `sympy.factorint` (Pollard rho/p−1, seconds, not a search) and cross-checked
here by the Lucas test itself — a wrong factor list fails `hprod`/`hprime` in the kernel, it is
not merely trusted. `a` and `b` each need one more recursive layer (`417677162933`, 39 bits, feeds
`a`; `22160661629` and `325086459374267`, 35/49 bits, feed `b`; the former needs its own leaf
`41655379`, 26 bits). Every OTHER factor at every level (2, 3, 463, 59, 1973, 897019, 89, 14923,
7, 19, 6942563, 509, 413527, 772231, 11, 2531, 115603, 1197907) is small enough for `norm_num`'s
own primality extension, mirroring exactly how `BN254/Primality.lean`'s leaves are closed.

Witnesses `g` (2, 3 or 5) were found by brute force over small candidates and verified against
BOTH Lucas conditions (Fermat `g^(n-1) ≡ 1` and non-triviality `g^((n-1)/q) ≢ 1` at every prime
factor `q`) before being committed to Lean — the same computed-outside/checked-inside discipline
`glvPallas`'s lattice-minimality argument used.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Import line: `import Dregg2.Circuit.Emit.PastaBasePrime`.
-/
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Crypto.BN254.Primality

namespace Dregg2.Circuit.Emit.PastaBasePrime

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Crypto.BN254.Primality (lucasList)

set_option autoImplicit false
-- The 255-bit `powModFuel` folds recurse ~255 levels; the kernel `decide` needs the headroom
-- (mirrors `BN254/Primality.lean`'s own `maxRecDepth 8000` for its 254-bit crown).
set_option maxRecDepth 8000

/-! ## §1 — the leaves that need their own recursive layer (everything else is `norm_num`). -/

theorem prime_41655379 : Nat.Prime 41655379 :=
  lucasList 41655379 2 26 [(2, 1), (3, 1), (6942563, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_417677162933 : Nat.Prime 417677162933 :=
  lucasList 417677162933 2 39 [(2, 2), (59, 1), (1973, 1), (897019, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_22160661629 : Nat.Prime 22160661629 :=
  lucasList 22160661629 3 35 [(2, 2), (7, 1), (19, 1), (41655379, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_41655379 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_325086459374267 : Nat.Prime 325086459374267 :=
  lucasList 325086459374267 2 49 [(2, 1), (509, 1), (413527, 1), (772231, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

/-! ## §2 — `a` and `b`, the two second-level factors of `pN − 1`. -/

theorem prime_539204044132271846773 : Nat.Prime 539204044132271846773 :=
  lucasList 539204044132271846773 5 69
    [(2, 2), (3, 5), (89, 1), (14923, 1), (417677162933, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_417677162933 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_8999194758858563409123804352480028797519453 :
    Nat.Prime 8999194758858563409123804352480028797519453 :=
  lucasList 8999194758858563409123804352480028797519453 2 143
    [(2, 2), (3, 4), (11, 1), (2531, 1), (115603, 1), (1197907, 1),
     (22160661629, 1), (325086459374267, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first
      | exact prime_22160661629 | exact prime_325086459374267 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

/-! ## §3 — the crown: `pN` itself. -/

/-- **`pN` is prime** — the Pallas base modulus, `pN − 1 = 2³²·3·463·a·b` with `a`, `b` the two
69/143-bit primes above. Machine-checked via the recursive Lucas/Pratt certificate; see the file
docstring for the factorization and witness provenance. -/
theorem prime_pN : Nat.Prime pN :=
  lucasList pN 5 255
    [(2, 32), (3, 1), (463, 1),
     (539204044132271846773, 1),
     (8999194758858563409123804352480028797519453, 1)]
    (by norm_num [pN]) (by norm_num [pN]) (by simp only [pN]; decide)
    (fun qe h => by fin_cases h <;> first
      | exact prime_539204044132271846773
      | exact prime_8999194758858563409123804352480028797519453
      | norm_num)
    (by simp only [pN]; decide) (fun qe h => by fin_cases h <;> (simp only [pN]; decide))

/-- The `Fact` instance the field/group tower downstream (`PastaGroupLaw`) consumes: with it in
scope, Mathlib's `[Fact p.Prime]`-gated `ZMod.instField` fires unconditionally. -/
instance : Fact (Nat.Prime pN) := ⟨prime_pN⟩

/-- `ZMod pN` is now a genuine `Field` (an `example`, not a fresh instance, to avoid a competing
`Field` diamond — the canonical instance is Mathlib's `ZMod.instField`). -/
noncomputable example : Field (ZMod pN) := inferInstance

#assert_axioms prime_41655379
#assert_axioms prime_417677162933
#assert_axioms prime_22160661629
#assert_axioms prime_325086459374267
#assert_axioms prime_539204044132271846773
#assert_axioms prime_8999194758858563409123804352480028797519453
#assert_axioms prime_pN

end Dregg2.Circuit.Emit.PastaBasePrime
