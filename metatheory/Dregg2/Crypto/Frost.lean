/-
# `Dregg2.Crypto.Frost` — the threshold-Schnorr (FROST) quorum certificate: a t-of-n cert IS a plain
Schnorr signature, verified by the single-signer verifier.

The federation's quorum certificate today is a weighted-threshold BLS aggregate (`BlsThreshold`),
which is constant-size but rests on a PAIRING carrier. FROST is the alternative the signature research
recommends: a threshold cert built on the DISCRETE-LOG carrier we already have (`SchnorrCurveField`),
adding NO new hardness assumption. Its defining property — and the reason it is worth modeling — is
that a FROST t-of-n signature is a SINGLE ordinary Schnorr signature `(R, z)`, verified by the EXACT
verifier a single signer uses (RFC 9591). So a dregg quorum certificate becomes "one signature under
the federation's group public key," CONSTANT-SIZE regardless of the validator count, and its
verification theorem is literally the Schnorr theorem.

The one new piece of algebra is Shamir/Lagrange reconstruction "in the exponent": the group secret `x`
is a degree-`(t-1)` polynomial's value at 0, and over any `t`-subset with Lagrange coefficients `lam`,
`x = Σ lam_i · x_i`. This file proves the load-bearing consequence — the Lagrange-combined partial
responses form exactly the group-key Schnorr response — so the combined certificate verifies under the
group public key with the single-signer verifier. Pure finite-field / module algebra; no carrier
beyond the DL hardness the Schnorr verifier already names.
-/
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic

namespace Dregg2.Crypto.Frost

open scoped BigOperators

variable {S : Type*} [Field S] {G : Type*} [AddCommGroup G] [Module S G]

/-- The single-signer Schnorr verification relation over an abstract prime-order group with generator
`g`: a signature `(R, z)` on challenge `e` verifies against public key `pk` iff `z · g = R + e · pk`.
This is the verifier a threshold cert reuses verbatim. -/
def SchnorrVerifies (g : G) (pk R : G) (e z : S) : Prop :=
  z • g = R + e • pk

/-- **A Schnorr signature under secret `x` verifies.** For public key `pk = x·g`, nonce commitment
`R = k·g`, and response `z = k + e·x`, the verification equation holds — the algebraic core every
Schnorr-family construction (single, multi, threshold) reuses. -/
theorem schnorr_sig_verifies (g : G) (x k e : S) :
    SchnorrVerifies g (x • g) (k • g) e (k + e * x) := by
  simp only [SchnorrVerifies, add_smul, mul_smul]

/-- **FROST reconstruction correctness — the quorum certificate is a group-key Schnorr signature.**

Given a `t`-subset `parts` of signers whose Lagrange coefficients `lam` reconstruct the group secret
`x = Σ_{i∈parts} lam_i · x_i` (the Shamir sharing evaluated at 0), each signer contributes nonce `k_i`
and partial response `z_i = k_i + e · (lam_i · x_i)`. The combined certificate `(R, z)` with
`R = (Σ k_i)·g` and `z = Σ z_i` equals the ordinary Schnorr signature `(K·g, K + e·x)` under the group
secret `x` — so it verifies under the group public key `pk = x·g` via `SchnorrVerifies`, the SAME
single-signer verifier, with NO dependence on `t`, `n`, or which subset signed. -/
theorem frost_cert_verifies_under_group_key {ι : Type*}
    (g : G) (parts : Finset ι) (shares lam k : ι → S) (x e : S)
    (hrecon : x = ∑ i ∈ parts, lam i * shares i) :
    SchnorrVerifies g (x • g)
      ((∑ i ∈ parts, k i) • g) e
      (∑ i ∈ parts, (k i + e * (lam i * shares i))) := by
  have hz : (∑ i ∈ parts, (k i + e * (lam i * shares i)))
      = (∑ i ∈ parts, k i) + e * x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hrecon]
  rw [hz]
  exact schnorr_sig_verifies g x (∑ i ∈ parts, k i) e

/-- **The certificate is constant-size.** Whatever the subset `parts`, the certificate is a single
`(R, z) : G × S` — one group element and one scalar — the same object a single signer produces.
(Stated as the trivial type-level fact that pins the "one signature, any committee size" property.) -/
theorem frost_cert_is_one_signature {ι : Type*}
    (g : G) (parts : Finset ι) (k : ι → S) (z : S) :
    ∃ cert : G × S, cert = ((∑ i ∈ parts, k i) • g, z) := ⟨_, rfl⟩

#assert_axioms schnorr_sig_verifies
#assert_axioms frost_cert_verifies_under_group_key

end Dregg2.Crypto.Frost
