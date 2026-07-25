/-
# Dregg2.Crypto.BN254 — the BN254 / Groth16 pairing model (root aggregator).

The Lean model of the BN254 pairing and the deployed Groth16 verify equation, built to instantiate
the abstract `verifyProof` oracle in `Market.ProtocolAssurance` and (with knowledge-soundness)
discharge `SettlementVerifier25Refines` (`ProtocolAssurance.lean:872`).

Layers (each `lake build`-verified, kernel-clean; `#assert_axioms` on stated theorems):

* `BN254.Fq`      — the base field `Fq = ZMod p` (`p` the BN254 base prime, ≠ the scalar `rBN254`);
                    `CommRing` unconditional, `Field` under the named `[Fact (Nat.Prime pBN254)]`.
* `BN254.Fp2`     — `Fp2 = Fq[u]/(u²+1)`; explicit coordinate `CommRing`, conjugation, norm.
* `BN254.Fp6`     — `Fp6 = Fp2[v]/(v³−ξ)`, `ξ = 9+u`; `CommRing`.
* `BN254.Fp12`    — `Fp12 = Fp6[w]/(w²−v)`; `CommRing` — the pairing's target field.
* `BN254.Curves`  — `G1 : y²=x³+3 /Fq` and the twist `G2 : y²=x³+b' /Fp2` (`b'=3/ξ`), on-curve
                    predicates + the standard generators (KATs), Mathlib `WeierstrassCurve` models.
* `BN254.Pairing` — the optimal-ate `pairing = finalExp ∘ millerLoop`; inverse-free Jacobian point
                    steps + denominator-eliminated line functions (DEFINITION); bilinearity /
                    non-degeneracy / faithfulness are the named OPEN goals.
* `BN254.Groth16` — the deployed 4-pairing + Pedersen-PoK 2-pairing verify EQUATION over the actual
                    `DreggGroth16Verifier25.sol` VK (every VK point on-curve, KAT'd) + the bridge
                    plan to `SettlementVerifier25Refines`.
* `BN254.Primality`— DISCHARGES the `Fq.lean` primality seam: `Nat.Prime pBN254` by a recursive
                    Pratt/Lucas certificate (kernel-checked, NO `sorry`/`axiom`/`native_decide`),
                    the `Fact` instance, and the ripple — `Field Fq`, `Field Fp2`, and the `G1`/`G2`
                    point `AddCommGroup`s all now unconditional; `Fp2FieldGoal` discharged.
* `BN254.TowerField`— DISCHARGES `Fp6FieldGoal` (`ξ` a non-cube) and `Fp12FieldGoal` (`v` a
                    non-square), both reduced to kernel-checked `Fp2` modexp non-residue certs
                    (fuel-structural `powMonFuel`, no `native_decide`); BUILDS `Field Fp6` and
                    `Field Fp12` (norm + explicit inverse), so the pairing target `Fp12` supports
                    INVERSION.  The whole tower is now genuine fields.
* `BN254.Bilinearity`— WIRES the pairing to the real point groups (`pairingP : G1Point × G2Point →
                    Fp12`, infinity ↦ 1) and states BILINEARITY non-vacuously over the group `+`/`•`
                    (`PairingBilinear{Left,Right}Goal`, `PairingScalar{Left,Right}Goal`; §5 KATs
                    kernel-compute the Miller value ≠ 1, so the equations bite).  PROVEN: `finalExp`
                    is a monoid hom (`finalExp_mul/one/pow`), the infinity cases, the scalar law at
                    `a=0,1`, and the reductions of each goal to a single NAMED Miller-loop residual
                    (`MillerQuasiMult{Left,Right}`, `MillerScalar{Left,Right}` — the Weil-reciprocity
                    / divisor cofactor `finalExp c = 1`), which is left OPEN, not faked.
-/
import Dregg2.Crypto.BN254.Fq
import Dregg2.Crypto.BN254.Fp2
import Dregg2.Crypto.BN254.Fp6
import Dregg2.Crypto.BN254.Fp12
import Dregg2.Crypto.BN254.Curves
import Dregg2.Crypto.BN254.Pairing
import Dregg2.Crypto.BN254.Groth16
import Dregg2.Crypto.BN254.Primality
import Dregg2.Crypto.BN254.TowerField
import Dregg2.Crypto.BN254.Bilinearity
