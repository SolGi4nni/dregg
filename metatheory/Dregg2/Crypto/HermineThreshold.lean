/-
# `Dregg2.Crypto.HermineThreshold` — the POST-QUANTUM threshold quorum certificate (Hermine), formalized.

`Frost.lean` proved the classical threshold-Schnorr quorum certificate over a prime-order group (the DL
carrier). This file is its POST-QUANTUM counterpart: the correctness core of **Hermine** (IACR ePrint
2026/419, Borin–Celi–del Pino–Espitau–Katsumata–Niot–Prest–Takemure), a lattice-based FROST-analog
threshold signature, presented at NIST MPTS 2026. Formalizing it is very plausibly a first for a
PQ-threshold scheme.

Why it formalizes as cleanly as classical FROST — and why we picked it over the other candidates:

* Hermine is built on **Raccoon**, which uses *Fiat–Shamir WITHOUT aborts* (noise-flooding, not
  rejection sampling). So the signing operation is a single LINEAR map, `z = y + c·s`, verified by the
  lattice relation `A·z = w + c·t` — no rejection-sampling loop, the messiest obstacle to formalizing
  the Dilithium family, is simply absent.
* Its threshold uses an *"everywhere-short"* (Vandermonde/Shamir) sharing with a **short LINEAR
  reconstruction** `s = Σ λ_i·s_i`. So partial signatures combine linearly — the EXACT structure as
  classical FROST — only over a module instead of a prime-order group.

We model the lattice map abstractly as an `R`-linear map `A : M →ₗ[R] N` (the public matrix). The
CORRECTNESS below is unconditional module algebra. The SECURITY (that `A·z = w + c·t` cannot be forged
without a short `s`) rests on the MLWE/MSIS lattice assumptions — a NEW carrier for dregg, but a
standard, cleanly-stateable one, named as a hypothesis where the unforgeability boundary is drawn (a
follow-on, like the Schnorr `SchnorrDLHard` carrier), NEVER a Lean axiom.
-/
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.LinearMap.Defs

namespace Dregg2.Crypto.HermineThreshold

open scoped BigOperators

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Lattice verification: a Raccoon/Hermine signature `z` verifies against public key `t = A·s`,
commitment `w = A·y`, and challenge `c` iff `A·z = w + c·t`. The lattice analog of `SchnorrVerifies`. -/
def verify (A : M →ₗ[R] N) (t w : N) (c : R) (z : M) : Prop :=
  A z = w + c • t

/-- **A Raccoon signature verifies** (single signer). Secret `s`, mask `y`, challenge `c`: the
signature `z = y + c·s`, with public key `t = A·s` and commitment `w = A·y`, satisfies the lattice
relation. No rejection sampling — one linear map. This is the algebraic core Hermine's threshold
reconstruction lifts. -/
theorem raccoon_sig_verifies (A : M →ₗ[R] N) (s y : M) (c : R) :
    verify A (A s) (A y) c (y + c • s) := by
  simp only [verify, map_add, map_smul]

/-- **Hermine threshold correctness — the PQ quorum certificate verifies under the group key.**

A `t`-subset `parts` of signers whose Vandermonde/Shamir coefficients `lam` linearly reconstruct the
group secret `s = Σ_{i∈parts} lam_i · s_i` (the "everywhere-short" reconstruction). Each signer
contributes mask `y_i` and partial signature `z_i = y_i + c · (lam_i · s_i)`. The combined certificate
`z = Σ z_i`, against group public key `t = A·s` and combined commitment `w = A·(Σ y_i)`, verifies the
lattice relation — with NO dependence on `t`, `n`, or which subset signed. This is the exact shape of
`Frost.frost_cert_verifies_under_group_key`, over a module: linear signing + linear reconstruction. -/
theorem hermine_cert_verifies_under_group_key {ι : Type*}
    (A : M →ₗ[R] N) (parts : Finset ι) (shares : ι → M) (lam : ι → R) (masks : ι → M)
    (s : M) (c : R) (hrecon : s = ∑ i ∈ parts, lam i • shares i) :
    verify A (A s) (A (∑ i ∈ parts, masks i)) c
      (∑ i ∈ parts, (masks i + c • (lam i • shares i))) := by
  have hz : (∑ i ∈ parts, (masks i + c • (lam i • shares i)))
      = (∑ i ∈ parts, masks i) + c • s := by
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← hrecon]
  rw [hz]
  exact raccoon_sig_verifies A s (∑ i ∈ parts, masks i) c

/-- **A share is a valid signature under its own key share** (Hermine's no-zero-shares property, the
basis of non-interactive identifiable abort): signer `i`'s partial `y_i + c·(lam_i·s_i)` verifies under
the key share `A·(lam_i·s_i)` with commitment `A·y_i`. So a bad share is CAUGHT by verifying it alone. -/
theorem hermine_share_is_valid_under_key_share {ι : Type*}
    (A : M →ₗ[R] N) (shares : ι → M) (lam : ι → R) (masks : ι → M) (c : R) (i : ι) :
    verify A (A (lam i • shares i)) (A (masks i)) c (masks i + c • (lam i • shares i)) :=
  raccoon_sig_verifies A (lam i • shares i) (masks i) c

#assert_axioms raccoon_sig_verifies
#assert_axioms hermine_cert_verifies_under_group_key
#assert_axioms hermine_share_is_valid_under_key_share

end Dregg2.Crypto.HermineThreshold
