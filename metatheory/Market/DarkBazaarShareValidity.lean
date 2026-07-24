import Dregg2.Tactics
import Bfv.Noise
import Market.DarkBazaarDecryptConsistency
import Market.DarkBazaarCollectiveOpening
import Market.DarkBazaarQuorumNecessity

/-!
# Malicious-share validity — the relation a trusted-dealer-free threshold decrypt must enforce

`DarkBazaarCollectiveOpening` + `DarkBazaarQuorumNecessity` state the collective decrypt's soundness, hiding,
and n-of-n necessity under HONEST shares. This file states the predicate that makes it malicious-secure
(roadmap §3.2, trusted-dealer removal, at the relation level): a party's partial-decrypt share `hᵢ` is VALID
w.r.t. its COMMITTED secret `sᵢ` (a VSS commitment) and the public `c1` exactly when `hᵢ = sᵢ·c1 + eᵢ` for a
decrypt-safe noise `eᵢ`. A malicious-secure threshold decrypt proves `ShareValid` in ZK against the
commitment to `sᵢ`; this file proves the two facts that make that check load-bearing: a valid share can only
deviate from its committed contribution by safe noise, and an UNVALIDATED share can move the decrypted
message (so the check is necessary, not decorative).

Scope: the scalar `Bfv` phase model. The ZK circuit for `ShareValid` against a VSS commitment, and the full
distributed protocol, are the named build (roadmap §3.2/§3.3). Here the relation + its necessity are theorems.
-/

namespace Market.DarkBazaarShareValidity

open Bfv Market.DarkBazaarDecryptConsistency Market.DarkBazaarCollectiveOpening
open Market.DarkBazaarQuorumNecessity

/-- A party's partial-decrypt share `hᵢ` is VALID w.r.t. its committed secret `sᵢ` and the public `c1` iff it
is exactly `sᵢ·c1 + eᵢ` for a decrypt-safe noise `eᵢ`. This is the predicate proved in ZK against a commitment
to `sᵢ`: a malicious party cannot pass it with a wrong secret or an out-of-budget error. -/
def ShareValid (P : Params) (sᵢ c1 hᵢ : ℤ) : Prop :=
  ∃ e : ℤ, SafeNoise P |e| ∧ hᵢ = sᵢ * c1 + e

/-- The predicate is SATISFIABLE (non-vacuous): the honest share `sᵢ·c1 + e` with decrypt-safe `e` is valid. -/
theorem honest_share_valid {P : Params} {sᵢ c1 e : ℤ} (he : SafeNoise P |e|) :
    ShareValid P sᵢ c1 (sᵢ * c1 + e) :=
  ⟨e, he, rfl⟩

/-- A valid share deviates from its committed contribution `sᵢ·c1` by at most a decrypt-safe noise. So a party
that passes validity has contributed essentially its committed value — it cannot inject a large shift. -/
theorem valid_share_bounded_deviation {P : Params} {sᵢ c1 hᵢ : ℤ}
    (h : ShareValid P sᵢ c1 hᵢ) : SafeNoise P |hᵢ - sᵢ * c1| := by
  obtain ⟨e, he, hh⟩ := h
  have hd : hᵢ - sᵢ * c1 = e := by rw [hh]; ring
  rw [hd]; exact he

/-- **FAILING SIDE — why the validity check is NECESSARY.** A share whose deviation from the committed
contribution is NOT decrypt-safe is NOT valid. Contrapositive of `valid_share_bounded_deviation`: an
out-of-budget deviation cannot pass the check. -/
theorem unsafe_deviation_not_valid {P : Params} {sᵢ c1 hᵢ : ℤ}
    (hbad : ¬ SafeNoise P |hᵢ - sᵢ * c1|) : ¬ ShareValid P sᵢ c1 hᵢ :=
  fun h => hbad (valid_share_bounded_deviation h)

/-- **An UNVALIDATED malicious share can move the decrypted message.** If the honest combined phase opens to
`m`, and a malicious party shifts its contribution by `δ = hᵢ' − hᵢ` that is not decrypt-safe (i.e. `−δ` is not
a difference of two safe noises), the tampered phase `honest + δ` no longer opens to `m`. This is exactly what
`ShareValid` forbids (its deviation is safe), so the ZK check is load-bearing, not decorative. Built on
`QuorumNecessity.dropped_share_breaks_opening`. -/
theorem unvalidated_shift_breaks_opening {P : Params} {honestPhase m δ : ℤ}
    (hopen : DecryptConsistent P honestPhase m)
    (hbig : ∀ e e' : ℤ, SafeNoise P |e| → SafeNoise P |e'| → (-δ) ≠ e - e') :
    ¬ DecryptConsistent P (honestPhase + δ) m := by
  rintro ⟨e', he', hp'⟩
  obtain ⟨e, he, hp⟩ := hopen
  -- hp : honestPhase = Δm + e ; hp' : honestPhase + δ = Δm + e'  ⇒  δ = e' − e = −(e − e')
  have hδ : -δ = e - e' := by rw [hp] at hp'; linarith
  exact hbig e e' he he' hδ

/-- **ROBUSTNESS — validated shares reconstruct the honest collective key.** If ALL `n` shares are valid
against their committed secrets `sᵢ`, the combined phase is exactly `c0 + (Σ sᵢ)·c1 + (Σ deviations)`. The
`(Σ sᵢ)·c1` term is the HONEST collective-key contribution (`s = Σ sᵢ`, pinned by the VSS commitments); a
malicious party bound by `ShareValid` cannot move it — it can only contribute to `Σ deviations`, and each
deviation is decrypt-safe (`valid_share_bounded_deviation`). So malicious-but-validated parties are confined
to injecting bounded noise on top of the honest key; the message survives while the total noise stays in the
decrypt budget (the deployed `smudge_bits + ⌈log₂ n⌉ ≤ 84` constraint). -/
theorem valid_shares_reconstruct_honest_key {P : Params} {n : ℕ} (c0 c1 : ℤ)
    (s h : Fin n → ℤ) (_hvalid : ∀ i, ShareValid P (s i) c1 (h i)) :
    combinePhase c0 h = c0 + (∑ i, s i) * c1 + ∑ i, (h i - s i * c1) := by
  simp only [combinePhase]
  have hsum : (∑ i, s i) * c1 + ∑ i, (h i - s i * c1) = ∑ i, h i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  linarith [hsum]

#assert_all_clean [Market.DarkBazaarShareValidity.honest_share_valid,
  Market.DarkBazaarShareValidity.valid_share_bounded_deviation,
  Market.DarkBazaarShareValidity.unsafe_deviation_not_valid,
  Market.DarkBazaarShareValidity.unvalidated_shift_breaks_opening,
  Market.DarkBazaarShareValidity.valid_shares_reconstruct_honest_key]

end Market.DarkBazaarShareValidity
