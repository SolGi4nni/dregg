import Dregg2.Tactics
import Market.DarkBazaarDecryptConsistency
import Market.DarkBazaarCollectiveOpening

/-!
# Quorum necessity — the n-of-n SOUNDNESS dual of the no-single-viewer hiding

`DarkBazaarCollectiveOpening` proves the collective decrypt (`s = Σ sᵢ`) is sound and that any `n−1`
coalition, with smudging, learns nothing (hiding). This file proves the *other* half of `n`-of-`n`: any
`n−1` coalition cannot DECRYPT either. Every party whose share carries real information is NECESSARY — drop
it and the opening breaks. Together: all `n` are needed to open, and any `n−1` learn nothing.

Scope: the scalar `Bfv` phase model, at the combined-phase level (the collective decrypt IS
`DecryptConsistent` at `combinePhase`, `collective_is_decryptConsistent`). The RNS-polynomial per-slot lift
and malicious-share validity are the named residuals (FHEGG-SAME-OPENING-APEX.md §3.2/§3.3).
-/

namespace Market.DarkBazaarQuorumNecessity

open Bfv Market.DarkBazaarDecryptConsistency Market.DarkBazaarCollectiveOpening

/-- **QUORUM NECESSITY.** If the FULL quorum opens the ciphertext to `m`, then dropping one party's share
`sj` (subtracting its contribution from the combined phase) breaks the opening — UNLESS `sj` is a difference
of two safe noises (that party contributed essentially nothing beyond noise). So a party whose share carries
real information is required: the `n−1` phase no longer decrypts to `m`. -/
theorem dropped_share_breaks_opening
    {P : Params} {fullPhase m sj : ℤ}
    (hfull : DecryptConsistent P fullPhase m)
    (hnontrivial : ∀ e e' : ℤ, SafeNoise P |e| → SafeNoise P |e'| → sj ≠ e - e') :
    ¬ DecryptConsistent P (fullPhase - sj) m := by
  rintro ⟨e', he', hp'⟩
  obtain ⟨e, he, hp⟩ := hfull
  have hsj : sj = e - e' := by linarith [hp, hp']
  exact hnontrivial e e' he he' hsj

/-- The collective form: dropping party `j`'s contribution from the full combined phase (`combinePhase −
shares j` is exactly the `n−1` combined phase, `c0 + ∑_{i≠j} shares i`) breaks the collective opening, under
the same non-triviality on that party's share. Ties the scalar law to `CollectiveOpensTo`. -/
theorem collective_missing_share_breaks
    {P : Params} {n : ℕ} {c0 : ℤ} {shares : Fin n → ℤ} {m : ℤ} {j : Fin n}
    (hfull : CollectiveOpensTo P c0 shares m)
    (hnontrivial : ∀ e e' : ℤ, SafeNoise P |e| → SafeNoise P |e'| → shares j ≠ e - e') :
    ¬ DecryptConsistent P (combinePhase c0 shares - shares j) m := by
  rw [collective_is_decryptConsistent] at hfull
  exact dropped_share_breaks_opening hfull hnontrivial

/-- **The failing side — the necessity condition is SHARP, not an over-strong guard.** If a party's share IS
a difference of two safe noises (it contributed nothing beyond noise), then dropping it does NOT break the
opening: the `n−1` phase still decrypts to `m`. So the non-triviality hypothesis above is exactly the
boundary — a genuinely-contributing share is necessary, a noise-only share is not. -/
theorem trivial_share_drop_still_opens
    {P : Params} {fullPhase m sj e e' : ℤ}
    (hfull : fullPhase = (P.Δ : ℤ) * m + e) (_he : SafeNoise P |e|)
    (he' : SafeNoise P |e'|) (hsj : sj = e - e') :
    DecryptConsistent P (fullPhase - sj) m := by
  refine ⟨e', he', ?_⟩
  rw [hfull, hsj]; ring

#assert_all_clean [Market.DarkBazaarQuorumNecessity.dropped_share_breaks_opening,
  Market.DarkBazaarQuorumNecessity.collective_missing_share_breaks,
  Market.DarkBazaarQuorumNecessity.trivial_share_drop_still_opens]

end Market.DarkBazaarQuorumNecessity
