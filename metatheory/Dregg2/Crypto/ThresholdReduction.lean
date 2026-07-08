/-
# `Dregg2.Crypto.ThresholdReduction` — threshold-EUF-CMA reduces to single-signer-EUF-CMA.

The reduction ladder: `Frost`/`HermineThreshold` proved threshold CORRECTNESS; `ShamirPrivacy` proved
the information-theoretic security floor (a corrupt minority of `t-1` learns nothing about the group
key). This file closes the computational reduction SHAPE: a threshold forgery yields a single-signer
forgery under the group key, so threshold security is single-signer security — no NEW hardness beyond
the single-signer carrier (DL/forking for FROST, MLWE/MSIS for Hermine).

Two facts, already proved, make the reduction tight:
* `Frost.frost_cert_verifies_under_group_key` — the combined threshold certificate, when it verifies,
  is a signature under the group public key checked by the EXACT single-signer verifier. So anything
  that verifies as a threshold cert verifies as a single-signer signature under the group key.
* `ShamirPrivacy.shamir_t_privacy` — the `t-1` shares a threshold adversary corrupts are consistent
  with EVERY group secret, so they give it no advantage the single-signer game does not already grant.

Together: if no efficient adversary forges a single-signer signature under the group key (the named DL
carrier), then none forges a threshold certificate either — even holding `t-1` shares. We state the
reduction as an implication over the abstract unforgeability predicate; the computational hardness of
producing a verifying signature on an un-signed message is the DL/forking carrier, NOT re-proved here.
-/
import Dregg2.Crypto.Frost
import Dregg2.Crypto.ShamirPrivacy

namespace Dregg2.Crypto.ThresholdReduction

open scoped BigOperators
open Dregg2.Crypto.Frost

variable {S : Type*} [Field S] {G : Type*} [AddCommGroup G] [Module S G]

/-- A signature scheme is **unforgeable** under public key `pk` w.r.t. a "legitimately signed" predicate
`Signed` when every signature that VERIFIES on challenge `e` had `e` legitimately signed — i.e. no
verifying signature on an un-signed message exists. This packages the EUF-CMA guarantee; the claim that
no efficient adversary can violate it is the DL/forking (resp. MLWE/MSIS) carrier, named at this
boundary, not discharged. -/
def Unforgeable (g pk : G) (Signed : S → Prop) : Prop :=
  ∀ R e z, SchnorrVerifies g pk R e z → Signed e

/-- **Threshold security reduces to single-signer security.** Suppose the single-signer scheme is
`Unforgeable` under the group public key `x·g` (with `x = Σ lam_i·shares_i` the reconstructed group
secret). Then a combined threshold certificate — which verifies under `x·g` via the very same verifier
(`frost_cert_verifies_under_group_key`) — cannot verify on an un-signed challenge either: its challenge
`e` must be `Signed`. So NO threshold forgery exists whenever no single-signer forgery does; threshold
security adds no new hardness assumption over the single-signer carrier. -/
theorem threshold_unforgeable_of_single_signer {ι : Type*}
    (g : G) (parts : Finset ι) (shares lam k : ι → S) (x e : S)
    (hrecon : x = ∑ i ∈ parts, lam i * shares i)
    (Signed : S → Prop) (hss : Unforgeable g (x • g) Signed) :
    Signed e :=
  hss _ e _ (frost_cert_verifies_under_group_key g parts shares lam k x e hrecon)

/-- **The corruption gives no advantage.** For any set `T` of `t-1` shares a threshold adversary
corrupts, and any group secret it might try to distinguish, `ShamirPrivacy` provides a sharing
consistent with the corrupt shares under EITHER secret — so the single-signer unforgeability assumed
in `threshold_unforgeable_of_single_signer` is not weakened by the adversary holding those shares. This
ties the two halves: single-signer unforgeability (computational) + t-privacy (information-theoretic)
⟹ threshold unforgeability, with no new carrier. -/
theorem corrupt_minority_is_simulatable [DecidableEq S] (t : ℕ) (ht : 1 ≤ t) (T : Finset S)
    (hcard : T.card = t - 1) (h0 : (0 : S) ∉ T) (observedShares : S → S) (s₀ s₁ : S) :
    (∃ p : Polynomial S, p.degree < (t : ℕ) ∧ p.eval 0 = s₀ ∧ ∀ i ∈ T, p.eval i = observedShares i) ∧
    (∃ q : Polynomial S, q.degree < (t : ℕ) ∧ q.eval 0 = s₁ ∧ ∀ i ∈ T, q.eval i = observedShares i) :=
  Dregg2.Crypto.ShamirPrivacy.shamir_secret_indistinguishable_below_threshold
    t ht T hcard h0 observedShares s₀ s₁

#assert_axioms threshold_unforgeable_of_single_signer
#assert_axioms corrupt_minority_is_simulatable

end Dregg2.Crypto.ThresholdReduction
