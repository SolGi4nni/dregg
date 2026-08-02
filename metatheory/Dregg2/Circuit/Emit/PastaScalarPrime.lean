/-
# Dregg2.Circuit.Emit.PastaScalarPrime — `Nat.Prime qN`, machine-checked: the Pallas SCALAR modulus.

## Why this file exists

`PastaBasePrime.lean` closed the *base* side: `Fact (Nat.Prime pN)`, hence `Field (ZMod pN)` by
Mathlib's `ZMod.instField`. That unlocked the `[Field F]` layer of `KimchiVerify` at `Fp` — the
cross-implementation differential's `permscalar` / `publiceval` / `ipab0` pairs.

It did **not** unlock `Fq`, and `Fq` is where half the Pickles work lives. `MinaWrapFtEval0`,
`MinaRealBlockGate` and the whole *deferred*/Wrap side compute in the Pallas SCALAR field: the IPA
challenges, `u_base`, the `ScalarChallenge::to_field` endo map on the Wrap side, `perm_scalars` for
a Wrap proof, and every scalar that multiplies a Pallas point. `scripts/pickles-crossimpl-
differential.sh` said so in its own words —

> "⚠ STILL UNREACHED, named rather than papered over: there is no `Fact (Nat.Prime qN)`, so
> `ZMod qN` — the field `MinaRealBlockGate`/`MinaWrapFtEval0` work at — is still not a `Field`."

— so every `Fq` pair in that differential was forced through `Nat`-modular spellings (`powFast`,
`bPolyMod`, `endoLift`) while the `[Field F]` definitions they mirror could not be instantiated
there at all. This file removes that, and §5 of the differential now sweeps the `Fq` side.

## The certificate (computed outside Lean, checked inside — the `pN` file's own method)

`Dregg2.Crypto.BN254.Primality`'s generic recursive Pratt/Lucas combinator (`powModFuel`,
`powModFuel_correct`, `lucasList`) is reused verbatim, exactly as `PastaBasePrime` reuses it.

`qN − 1 = 2³² · 3² · 1709 · 24859 · A · B`, where
  `A = 1690502597179744445941507` (81 bits) and
  `B = 10427374428728808478656897599072717` (114 bits),
fully factored by `sympy.factorint` and cross-checked here by the Lucas test itself — a wrong
factor list fails `hprod`/`hprime` in the kernel, it is not merely trusted.

The recursion is **shallower and cheaper than `pN`'s**: `A` needs two children (`4129989133`,
32 bits, and `5247740253619`, 43 bits — the latter needing one more leaf, `80513981`, 27 bits);
`B` needs two (`399082391`, 29 bits, and `5239247429827`, 43 bits). Every other factor at every
level (2, 3, 5, 7, 13, 17, 71, 359, 757, 1709, 12149, 24859, 31649, 294793, 958679, 4025699,
4229279, 5701177) is under 2²³ and closed by `norm_num`'s own primality extension — `pN`'s tree
needed leaves up to 6942563 and second-level factors at 69 and 143 bits.

Witnesses `g` (2, 5 or 7) were found by brute force over small candidates and verified against BOTH
Lucas conditions (Fermat `g^(n−1) ≡ 1` and non-triviality `g^((n−1)/q) ≢ 1` at every prime factor
`q`) before being committed to Lean.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Import line: `import Dregg2.Circuit.Emit.PastaScalarPrime`.
-/
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Crypto.BN254.Primality

namespace Dregg2.Circuit.Emit.PastaScalarPrime

open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Crypto.BN254.Primality (lucasList)

set_option autoImplicit false
-- The 255-bit `powModFuel` folds recurse ~255 levels; the kernel `decide` needs the headroom
-- (mirrors `PastaBasePrime.lean` / `BN254/Primality.lean`).
set_option maxRecDepth 8000

/-! ## §1 — the leaves that need their own recursive layer (everything else is `norm_num`). -/

theorem prime_80513981 : Nat.Prime 80513981 :=
  lucasList 80513981 2 27 [(2, 2), (5, 1), (4025699, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_399082391 : Nat.Prime 399082391 :=
  lucasList 399082391 7 29 [(2, 1), (5, 1), (7, 1), (5701177, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_4129989133 : Nat.Prime 4129989133 :=
  lucasList 4129989133 5 32 [(2, 2), (3, 1), (359, 1), (958679, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_5239247429827 : Nat.Prime 5239247429827 :=
  lucasList 5239247429827 2 43 [(2, 1), (3, 2), (757, 1), (12149, 1), (31649, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_5247740253619 : Nat.Prime 5247740253619 :=
  lucasList 5247740253619 2 43 [(2, 1), (3, 3), (17, 1), (71, 1), (80513981, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first | exact prime_80513981 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

/-! ## §2 — `A` and `B`, the two second-level factors of `qN − 1`. -/

theorem prime_1690502597179744445941507 : Nat.Prime 1690502597179744445941507 :=
  lucasList 1690502597179744445941507 2 81
    [(2, 1), (3, 1), (13, 1), (4129989133, 1), (5247740253619, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first
      | exact prime_4129989133 | exact prime_5247740253619 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

theorem prime_10427374428728808478656897599072717 :
    Nat.Prime 10427374428728808478656897599072717 :=
  lucasList 10427374428728808478656897599072717 2 114
    [(2, 2), (294793, 1), (4229279, 1), (399082391, 1), (5239247429827, 1)]
    (by norm_num) (by norm_num) (by decide)
    (fun qe h => by fin_cases h <;> first
      | exact prime_399082391 | exact prime_5239247429827 | norm_num)
    (by decide) (fun qe h => by fin_cases h <;> decide)

/-! ## §3 — the crown: `qN` itself. -/

/-- **`qN` is prime** — the Pallas scalar / Vesta base modulus,
`qN − 1 = 2³²·3²·1709·24859·A·B` with `A`, `B` the 81/114-bit primes above. Machine-checked via
the recursive Lucas/Pratt certificate; see the file docstring for factorization and witness
provenance. -/
theorem prime_qN : Nat.Prime qN :=
  lucasList qN 5 255
    [(2, 32), (3, 2), (1709, 1), (24859, 1),
     (1690502597179744445941507, 1),
     (10427374428728808478656897599072717, 1)]
    (by norm_num [qN]) (by norm_num [qN]) (by simp only [qN]; decide)
    (fun qe h => by fin_cases h <;> first
      | exact prime_1690502597179744445941507
      | exact prime_10427374428728808478656897599072717
      | norm_num)
    (by simp only [qN]; decide) (fun qe h => by fin_cases h <;> (simp only [qN]; decide))

/-- The `Fact` instance the `Fq` side consumes: with it in scope, Mathlib's `[Fact p.Prime]`-gated
`ZMod.instField` fires unconditionally at `ZMod qN`. -/
instance : Fact (Nat.Prime qN) := ⟨prime_qN⟩

/-- `ZMod qN` is now a genuine `Field` (an `example`, not a fresh instance, to avoid a competing
`Field` diamond — the canonical instance is Mathlib's `ZMod.instField`). -/
noncomputable example : Field (ZMod qN) := inferInstance

-- …and it is **computable**, which is what makes the `Fq` half of the cross-implementation
-- differential possible at all: inversion runs under the interpreter, no `noncomputable` marker.
#guard (7 : ZMod qN)⁻¹ * 7 == 1

/-- The two Pasta moduli are distinct primes, so `Fp` and `Fq` are genuinely two fields — pinned
here because every "the scalar side" claim downstream depends on not having proved `pN` twice. -/
theorem qN_ne_pN : qN ≠ Dregg2.Circuit.Emit.PastaField.pN := by
  simp only [qN, Dregg2.Circuit.Emit.PastaField.pN]; decide

#assert_axioms prime_80513981
#assert_axioms prime_399082391
#assert_axioms prime_4129989133
#assert_axioms prime_5239247429827
#assert_axioms prime_5247740253619
#assert_axioms prime_1690502597179744445941507
#assert_axioms prime_10427374428728808478656897599072717
#assert_axioms prime_qN
#assert_axioms qN_ne_pN

end Dregg2.Circuit.Emit.PastaScalarPrime
