/-
# Dregg2.Crypto.BN254.Fq — the BN254 **base** field `F_p`.

This is the FIRST brick of the Groth16/BN254 pairing model that instantiates the abstract
`verifyProof` oracle in `Market.ProtocolAssurance` and discharges `SettlementVerifier25Refines`
(the single highest-value named soundness hole; `ProtocolAssurance.lean:872`).

The gnark WRAPPED-R1CS circuit already modeled in `Dregg2.Circuit.R1csFr` lives over the BN254
**scalar** field `Fr = ZMod rBN254`.  The *pairing* — the object the deployed Solidity verifier
`DreggGroth16Verifier25.verifyProof` actually computes — lives over the **base** field `F_p`, a
DIFFERENT prime.  This module fixes `p` and `Fq := ZMod p`; `Fp2/Fp6/Fp12` (the tower) and the two
curves `G1/G2` are built on top in sibling files.

  * `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
    (the Solidity constant `P = 0x30644e72…d87cfd47`).  Distinct from the scalar
    `r = 0x30644e72…f0000001 = rBN254`.
  * `Fq := ZMod p`.  `CommRing` is automatic (all the tower's RING arithmetic uses only this) and
    `Nontrivial` follows from `1 < p`.

## The primality seam — named, not laundered, not axiomatized.

`Fq` is a FIELD iff `p` is prime, and `p` is prime — but a machine-checked proof needs a Pratt /
Lucas certificate (`Mathlib.NumberTheory.LucasPrimality.lucas_primality`, present at this pin),
since `norm_num`'s primality extension tops out near 25 bits and `p` is 254 bits.  We do NOT
discharge it here and we do NOT axiomatize it.  Instead the `Field`-requiring lemmas downstream
carry `[Fact (Nat.Prime pBN254)]` as an explicit instance hypothesis — the standard Mathlib idiom
for a checkable number-theoretic fact (NOT a cryptographic assumption).  `BN254BasePrimeGoal`
names the obligation so the discharge lane is visible; nothing in this file's `#guard`s or theorems
uses primality.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Dregg2.Tactics

namespace Dregg2.Crypto.BN254

set_option autoImplicit false

/-! ## §1 The base prime `p` and the field `Fq = ZMod p`. -/

/-- The BN254 base-field modulus `p` (Solidity `P = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`):
the order of the field over which the alt_bn128 curve `E : y² = x³ + 3` and the whole pairing are
defined.  Distinct from the scalar `rBN254`. -/
def pBN254 : ℕ :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- **Fq** — the BN254 base field as `ZMod pBN254`.  `CommRing` (everything the `Fp2/Fp6/Fp12`
tower's arithmetic consumes) is automatic; the `Field` upgrade is the named primality seam. -/
abbrev Fq : Type := ZMod pBN254

instance : Fact (1 < pBN254) := ⟨by norm_num [pBN254]⟩
instance : NeZero pBN254 := ⟨by norm_num [pBN254]⟩

example : CommRing Fq := inferInstance
example : Nontrivial Fq := inferInstance
example : DecidableEq Fq := inferInstance

/-! ## §2 The primality obligation (named; the Field structure is conditional on it). -/

/-- **The BN254 base-field primality obligation.**  `True` and in-principle provable via a
Pratt/Lucas certificate; the discharge lane (a recursive certificate over the factorization of
`p - 1`) is genuine follow-up work, deliberately NOT done here and NOT axiomatized. -/
def BN254BasePrimeGoal : Prop := Nat.Prime pBN254

/-- Under the named primality hypothesis `Fq` is a genuine field — the honest conditional form.
`Field (ZMod p)` is Mathlib's `[Fact p.Prime]`-gated instance; we merely record that it applies. -/
example [Fact (Nat.Prime pBN254)] : Field Fq := inferInstance

/-! ## §3 KAT sanity checks tying `Fq` to the deployed constants. -/

/-- The base prime and the scalar prime are DIFFERENT (a real bug-magnet the tower must respect:
the circuit is over `Fr`, the pairing over `Fq`). -/
theorem pBN254_ne_rBN254 : pBN254 ≠ 21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  norm_num [pBN254]

-- `p ≡ 3 (mod 4)` — the fact the deployed `sqrt_Fp` relies on (`EXP_SQRT_FP = (P+1)/4`,
-- the Tonelli–Shanks shortcut for `p ≡ 3 mod 4`).
#guard pBN254 % 4 = 3

-- `p ≡ 1 (mod 6)` — required for the sextic twist / the `Fp6` construction `v³ = 9 + u`.
#guard pBN254 % 6 = 1

-- The cast of `p - 1` into `Fq` is `-1` (basic field sanity).
#guard (((pBN254 - 1 : ℕ) : Fq) = -1)

-- The curve constant `b = 3` is nonzero in `Fq`.
#guard (3 : Fq) ≠ 0

#assert_axioms pBN254_ne_rBN254

end Dregg2.Crypto.BN254
