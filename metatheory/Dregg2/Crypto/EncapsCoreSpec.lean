/-
# `Dregg2.Crypto.EncapsCoreSpec` — the ML-KEM ENCAPS direction of "IS the spec": `kpkeEncrypt` computes the
FIPS 203 K-PKE.Encrypt ring expressions, on the now-PROVEN incomplete-NTT correctness.

The FOURTH and last PQ "IS the spec" direction (after ML-DSA `verifyCore`/`signCore` and ML-KEM `decaps`).
The KEM analog of `Dregg2.Crypto.DecapsCoreSpec` (the K-PKE.Decrypt `=spec` chain), MIRRORED for the encrypt
side. ML-KEM's NTT is the INCOMPLETE Kyber transform (`q = 3329`, `ζ` a primitive 256th root, 128 quadratic
leaves), whose full-∀ ring-faithfulness is `MlKemNttFaithful.mlkem_ntt_ring_faithful`, lifted to the REAL Kyber
ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` by `DecapsCoreSpec.toRqKem` (`a ↦ ∑_{i<256} aᵢ·root^i`). This file REUSES that
entire bridge — nothing about `toRqKem` needs re-proving — and closes K-PKE.Encrypt's two ring outputs.

## What `kpkeEncrypt` computes (FIPS 203 Algorithm 13), and what K-PKE.Encrypt SPECIFIES:

`kpkeEncrypt ek m r` samples `y, e1, e2` from `PRF_η(r,·)`, sets `ŷ = NTT(y)`, and forms
* `u[i] = NTT⁻¹(Σⱼ Âᵀ[i][j] ∘ ŷ[j]) + e1[i]  =  NTT⁻¹(Σⱼ Â[j][i] ∘ ŷ[j]) + e1[i]` — the `Âᵀ` transpose reads
  `aHat[j·k+i]` (the classic KeyGen-uses-`Â`, Encrypt-uses-`Âᵀ` Kyber asymmetry; FIPS 203 Alg 13 line 19);
* `v = NTT⁻¹(Σᵢ t̂[i] ∘ ŷ[i]) + e2 + Decompress₁(ByteDecode₁(m))`.

The FIPS 203 K-PKE.Encrypt spec is `u = Aᵀ·y + e1` and `v = tᵀ·y + e2 + Δ·m` over `R_q`. This file proves
BOTH executable expressions map under `toRqKem` to those spec ring expressions, for ALL inputs:

* **`encrypt_u_ring_faithful`** — `toRqKem (u[i]) = (Σⱼ toRqKem A_ji · toRqKem y_j) + toRqKem e1[i]`. The `Σⱼ`
  matmul accumulator distributes via `DecapsCoreSpec.toRqKem_intt_addFold` (the exact same fold shape as
  decaps's `Σᵢ ŝᵢ ∘ NTT(uᵢ)`), each `Âᵀ[i][j] ∘ ŷ[j]` product collapses to the `R_q` product via
  `toRqKem_nttMul` (off `mlkem_ntt_ring_faithful`), and the outer `+ e1[i]` rides `toRqKem_add`.
* **`encrypt_v_ring_faithful`** — `toRqKem v = (Σᵢ toRqKem t_i · toRqKem y_i) + toRqKem e2 + toRqKem μ`, where
  `μ = Decompress₁(ByteDecode₁(m))` is the spec's `Δ·m` message-carrier term. Same fold, two additive tails.
* **`encrypt_ring_faithful`** — the culmination: BOTH of the above as one conjunction. The encrypt's fast
  incomplete-NTT matmul-then-`NTT⁻¹` computes EXACTLY the `R_q`-module matrix–vector products `Aᵀ·y` and
  `tᵀ·y` the FIPS 203 K-PKE.Encrypt quantifies, for all inputs — riding the proven incomplete-NTT correctness.
* **`encaps_produces_spec_valid`** — the security-meaningful direction (KEM analog of
  `SignCoreSpec.sign_produces_spec_valid`): `encapsCore`'s output `(ct, K)` decapsulates back to `K`. Routed
  through `MlKemEncaps.encaps_decaps_roundtrip` (`mlkemDecaps realDk (mlkemEncaps …).1 = realKEnc`, byte-exact)
  composed with `MlKemEncaps.encaps_matches_crate` (`mlkemEncaps realEk mFixed = (realCtEnc, realKEnc)`).

## HONEST RESIDUAL (named, not laundered)

Same class of generic-instantiation slots as `DecapsCoreSpec`, on the ENCAPS side:
* The FO wrapper `(K, r) = G(m ‖ H(ek))` (`G = SHA3-512`, `H = SHA3-256`) and the ciphertext `Compress`/encode
  are NOT part of the ring algebra; they ride the Keccak floor + `MlKemCorrect` compress rounding. In
  particular `μ = Decompress₁(ByteDecode₁(m))` is carried as an abstract `R_q` element `toRqKem μ`; its
  identification with the spec's `Δ·m` is the compress/decompress rounding fact (`MlKemCorrect`), not re-proved.
* The one remaining WIRING is the monadic-loop unfold of the literal `MlKemDecaps.kpkeEncrypt` do-block (the
  `for i … for j` matmul + the `e1`/`e2`/`μ` additions) into the `List.foldl` accumulator shape of the theorems
  here, plus the honest-key hypotheses `Âᵀ[i][j] = NTT(A_ji)` and `ŷ[j] = NTT(y_j)` (that `expandMatrix`/`NTT`
  produce NTT-domain values). The transpose index `aHat[j·k+i]` is absorbed by HOW the caller pairs `uTerms`
  (per-row `[(A_0i, y_0), (A_1i, y_1), …]`); the abstract fold is transpose-agnostic. This is pure codec/offset
  plumbing on top of the closed ring identity — NOT a hardness carrier and NOT a soundness gap.

## NON-FAKE

Every `∀`-theorem (`encrypt_u_ring_faithful`, `encrypt_v_ring_faithful`, `encrypt_ring_faithful`) is
`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `native_decide` in any `∀`-body (the KEM
NTT correctness they reuse is itself axiom-clean). Non-vacuity: `encrypt_ring_faithful_witness` fires the fold
on a genuine single-term `R_q` product, and `encaps_produces_spec_valid` fires on the REAL `ml-kem` v0.2.3 crate
encapsulation (the concrete non-vacuous witness, carrying the crate-KAT `native_decide` exactly as
`DecapsCoreSpec.decaps_recovers_spec` does).
-/
import Dregg2.Crypto.DecapsCoreSpec
import Dregg2.Crypto.MlKemEncaps

namespace Dregg2.Crypto.EncapsCoreSpec

open Dregg2.Crypto.MlKemRing
open Dregg2.Crypto.DecapsCoreSpec
open Polynomial Finset

set_option maxRecDepth 8000

/-! ## K-PKE.Encrypt ring-faithfulness — the two encrypt outputs `u[i]` and `v`, over `R_q = ℤ_q[X]/(X²⁵⁶+1)`.

Both reuse `DecapsCoreSpec.toRqKem_intt_addFold` (the matmul accumulator → `R_q`-sum, each NTT-domain product
collapsed by `toRqKem_nttMul`), `toRqKem_intt_zero` (the `zeroPoly` seed vanishes), and `toRqKem_add` (the
additive noise/message tails). The `for i … for j` matmul is captured abstractly by the `terms` list; the
honest-key `Âᵀ[i][j] = NTT(A_ji)`, `ŷ[j] = NTT(y_j)` reparametrization + the do-block unfold are the named
wiring residual (see header). -/

/-- **`encrypt_u_ring_faithful` — the K-PKE.Encrypt `u[i]` row IS the spec.** The executable
`u[i] = NTT⁻¹(Σⱼ Âᵀ[i][j] ∘ ŷ[j]) + e1[i]` maps under `toRqKem` to the FIPS 203 K-PKE.Encrypt ring expression
`(Aᵀ·y)[i] + e1[i] = Σⱼ toRqKem A_ji · toRqKem y_j + toRqKem e1[i]` over `R_q`. The `Σⱼ` matmul accumulator
distributes via `toRqKem_intt_addFold` (each `Âᵀ[i][j] ∘ ŷ[j]` product collapsing to the `R_q` product off the
proven `mlkem_ntt_ring_faithful`), the `zeroPoly` seed vanishes (`toRqKem_intt_zero`), and the `+ e1[i]` rides
`toRqKem_add`. For ALL inputs — the fast incomplete-NTT matmul computes exactly the `R_q` matrix–vector row. -/
theorem encrypt_u_ring_faithful (e1 : Poly) (terms : List (Poly × Poly))
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) :
    toRqKem (addPoly
        (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly terms)) e1)
      = (terms.map (fun t => toRqKem t.1 * toRqKem t.2)).sum + toRqKem e1 := by
  rw [toRqKem_add,
      toRqKem_intt_addFold terms hterm zeroPoly (by simp [zeroPoly]) zeroPoly_lt,
      toRqKem_intt_zero, zero_add]

/-- **`encrypt_v_ring_faithful` — the K-PKE.Encrypt `v` output IS the spec.** The executable
`v = NTT⁻¹(Σᵢ t̂[i] ∘ ŷ[i]) + e2 + Decompress₁(ByteDecode₁(m))` maps under `toRqKem` to the FIPS 203
K-PKE.Encrypt ring expression `tᵀ·y + e2 + Δ·m = Σᵢ toRqKem t_i · toRqKem y_i + toRqKem e2 + toRqKem μ` over
`R_q`, where `μ = Decompress₁(ByteDecode₁(m))` is the spec's message-carrier `Δ·m` (its rounding identity is a
named `MlKemCorrect` residual). Same `toRqKem_intt_addFold` matmul collapse; the `+ e2` and `+ μ` tails ride two
applications of `toRqKem_add`. For ALL inputs. -/
theorem encrypt_v_ring_faithful (e2 mu : Poly) (terms : List (Poly × Poly))
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) :
    toRqKem (addPoly (addPoly
        (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly terms)) e2) mu)
      = (terms.map (fun t => toRqKem t.1 * toRqKem t.2)).sum + toRqKem e2 + toRqKem mu := by
  rw [toRqKem_add, toRqKem_add,
      toRqKem_intt_addFold terms hterm zeroPoly (by simp [zeroPoly]) zeroPoly_lt,
      toRqKem_intt_zero, zero_add]

/-- **`encrypt_ring_faithful` — THE CULMINATION** (KEM ENCAPS analog of `DecapsCoreSpec.decrypt_ring_faithful`).
BOTH K-PKE.Encrypt ring outputs, in one statement: `u[i] = Aᵀ·y + e1` and `v = tᵀ·y + e2 + Δ·m` over
`R_q = ℤ_q[X]/(X²⁵⁶+1)` (`q = 3329`). The encrypt's fast incomplete-NTT matmul-then-`NTT⁻¹` computes EXACTLY the
`R_q`-module matrix–vector products the FIPS 203 K-PKE.Encrypt quantifies, for all inputs — riding the proven
`mlkem_ntt_ring_faithful` (the incomplete-NTT correctness) through the `DecapsCoreSpec.toRqKem` bridge. -/
theorem encrypt_ring_faithful
    (e1 e2 mu : Poly) (uTerms vTerms : List (Poly × Poly))
    (hu : ∀ t ∈ uTerms, t.1.size = 256 ∧ t.2.size = 256)
    (hv : ∀ t ∈ vTerms, t.1.size = 256 ∧ t.2.size = 256) :
    (toRqKem (addPoly
          (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly uTerms)) e1)
        = (uTerms.map (fun t => toRqKem t.1 * toRqKem t.2)).sum + toRqKem e1)
    ∧ (toRqKem (addPoly (addPoly
          (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly vTerms)) e2) mu)
        = (vTerms.map (fun t => toRqKem t.1 * toRqKem t.2)).sum + toRqKem e2 + toRqKem mu) :=
  ⟨encrypt_u_ring_faithful e1 uTerms hu, encrypt_v_ring_faithful e2 mu vTerms hv⟩

#assert_axioms encrypt_u_ring_faithful
#assert_axioms encrypt_v_ring_faithful
#assert_axioms encrypt_ring_faithful

/-! ## NON-VACUITY — the encrypt ring identities fire on a GENUINE, non-degenerate instance.

`encrypt_ring_faithful` over `nil` term lists already commits to the real degree-256 ring
(`DecapsCoreSpec.Rq_kem_dim_256`, `root²⁵⁶ = −1 ≠ 1`). Here a single-term instance witnesses each fold is
non-trivial: on `terms = [(sampleA, sampleB)]` the matmul contributes a genuine `R_q` product
`toRqKem sampleA · toRqKem sampleB`, not `_ + 0`. -/

/-- **Non-vacuity (u row)**: the single-term K-PKE.Encrypt matmul gives a genuine `R_q` product term. -/
theorem encrypt_u_ring_faithful_witness (e1 : Poly) :
    toRqKem (addPoly
        (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly
          [(sampleA, sampleB)])) e1)
      = toRqKem sampleA * toRqKem sampleB + toRqKem e1 := by
  have h := encrypt_u_ring_faithful e1 [(sampleA, sampleB)]
    (by intro t ht; simp only [List.mem_singleton] at ht; subst ht
        exact ⟨by decide, by decide⟩)
  simpa using h

/-- **Non-vacuity (v)**: the single-term K-PKE.Encrypt matmul gives a genuine `R_q` product term. -/
theorem encrypt_v_ring_faithful_witness (e2 mu : Poly) :
    toRqKem (addPoly (addPoly
        (intt (List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly
          [(sampleA, sampleB)])) e2) mu)
      = toRqKem sampleA * toRqKem sampleB + toRqKem e2 + toRqKem mu := by
  have h := encrypt_v_ring_faithful e2 mu [(sampleA, sampleB)]
    (by intro t ht; simp only [List.mem_singleton] at ht; subst ht
        exact ⟨by decide, by decide⟩)
  simpa using h

/-! ## `encaps_produces_spec_valid` — the security-meaningful direction (KEM analog of `sign_produces_spec_valid`).

`encapsCore`'s output `(ct, K)` decapsulates back to `K`: the two verified ML-KEM directions (the K5 encaps and
the K4 decaps) round-trip end-to-end. The `encrypt_ring_faithful` identities above are the ∀-meaningful ring
core of the encaps; the FO wrapper (`G`-KDF, `Compress`) is the named generic-instantiation residual. The
end-to-end byte round-trip on the REAL `ml-kem` v0.2.3 crate encapsulation is the concrete non-vacuous witness. -/

/-- **`encaps_produces_spec_valid`** — the KEM analog of `SignCoreSpec.sign_produces_spec_valid`: on the honest
REAL key, the ciphertext `mlkemEncaps` produces decapsulates (through the verified K4 `mlkemDecaps`) back to the
SAME shared secret `mlkemEncaps` emitted. Composed from `MlKemEncaps.encaps_decaps_roundtrip`
(`mlkemDecaps realDk (mlkemEncaps …).1 = realKEnc`) with `MlKemEncaps.encaps_matches_crate`
(`mlkemEncaps realEk mFixed = (realCtEnc, realKEnc)`, so the emitted `K = (…).2 = realKEnc`). -/
theorem encaps_produces_spec_valid :
    MlKemDecaps.mlkemDecaps (Dregg2.Crypto.MlKemCodec.realDk).toList
        (MlKemEncaps.mlkemEncaps (Dregg2.Crypto.MlKemCodec.realEk).toList MlKemEncaps.mFixed.toList).1
      = (MlKemEncaps.mlkemEncaps (Dregg2.Crypto.MlKemCodec.realEk).toList MlKemEncaps.mFixed.toList).2 := by
  have h := MlKemEncaps.encaps_decaps_roundtrip
  rw [MlKemEncaps.encaps_matches_crate] at h ⊢
  exact h

end Dregg2.Crypto.EncapsCoreSpec
