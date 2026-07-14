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
open Dregg2.Crypto.MlKemCodec (ekDecode ctEncode byteEncode byteDecode decompressPoly paramK dCoeff)
open Dregg2.Crypto.MlKemSample (expandMatrix samplePolyCBD)
open Dregg2.Crypto.MlKemDecaps (kpkeEncrypt prf)
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

/-! ## BYTE-LEVEL LIFT — the literal `MlKemDecaps.kpkeEncrypt` do-block IS `ctEncode(Compress(u), Compress(v))`
of the FIPS 203 K-PKE.Encrypt ring outputs `u`, `v`.

`encrypt_{u,v}_ring_faithful` proved the ring identity on the abstract `List.foldl` accumulator shapes. This
section lifts them to the LITERAL executable `MlKemDecaps.kpkeEncrypt` do-block (the ENCAPS mirror of decaps's
`decWFold`/`kpkeDecrypt_unfold`/`decWFold_eq_terms`/`decryptW_eq_spec`/`kpkeDecrypt_eq_spec`). The wrinkle vs
decaps's single decrypt loop: encaps runs SIX loops (`y`, `e1`, `ŷ`, the nested `for i for j` matmul for `u`,
the `v` matmul) with threaded mutable state — all collapse through the same `forIn_eq_forIn_range'` /
`forIn_pure_yield_eq_foldl` opaque-`f` route to explicit `List.foldl`s (`kpkeEncrypt_unfold`), the nested
matmul becoming a `List.foldl`-of-`List.foldl`.

* **`encY`/`encE1`/`encE2`/`encYHat`/`encAHat`/`encTHat`/`encMu`** — the do-block's sampled/decoded pieces as
  explicit folds (mirroring the `mut`-state desugaring exactly): `y, e1` from `PRF_η(r,·)` with the threaded
  counter `n`, `e2 = PRF_η(r, 2k)`, `ŷ[j] = NTT(y[j])`, `Â = ExpandA(ρ)`, `t̂ = ekDecode ek`,
  `μ = Decompress₁(ByteDecode₁(m))`.
* **`encUFold`/`encVFold`/`encUArr`/`encV`** — the K-PKE.Encrypt `u`-row / `v` accumulators and their outputs
  `u[i] = NTT⁻¹(Σⱼ Âᵀ[i][j] ∘ ŷ[j]) + e1[i]`, `v = NTT⁻¹(Σᵢ t̂[i] ∘ ŷ[i]) + e2 + μ`.
* **`kpkeEncrypt_unfold`** — the do-block IS `ctEncode (encUArr, encV)` (pure monadic-loop plumbing, no
  `native_decide`).
* **`encUFold_eq_terms`/`encVFold_eq_terms`** — the honest-key reindex: on `Âᵀ[i][j] = NTT(A_ji)` and
  `t̂[i] = NTT(t_i)` (the NTT-domain matrix/vector the FIPS 203 KeyGen/ExpandA store), the index-folds equal
  `encrypt_{u,v}_ring_faithful`'s pair-folds over `terms` (`List.foldl_map` + `foldl_ext_mem`); `ŷ[j] = NTT(y_j)`
  is automatic (`encYHat_getElem`, no hypothesis).
* **`encryptU_eq_spec`/`encryptV_eq_spec`/`kpkeEncrypt_eq_spec`** — composing: the `R_q` elements `u[i]`, `v`
  that `kpkeEncrypt` feeds to `Compress`/`ctEncode` map under `toRqKem` to the FIPS 203 K-PKE.Encrypt
  expressions `Σⱼ A_ji·y_j + e1[i]` and `Σᵢ t_i·y_i + e2 + μ` over `R_q` — the ENCAPS byte-level `=spec`.

## HONEST RESIDUAL (named, not laundered)

Same class as `DecapsCoreSpec`, on the ENCAPS side: the ciphertext `Compress_{du}`/`Compress_{dv}` + `ByteEncode`
(`ctEncode`) rounding is `MlKemCorrect`'s compress rounding, not part of the ring algebra; `μ`'s identification
with the spec's `Δ·m` is the `Decompress₁∘ByteDecode₁` rounding fact; the FO `(K,r) = G(m ‖ H(ek))` KDF rides
the Keccak floor. `kpkeEncrypt_eq_spec` relates the ALREADY-computed ring elements (the `u[i]`, `v` arguments to
`Compress`), which is where the ring-faithfulness lives. -/

/-- `List.foldl (·.push (f ·)) acc = acc ++ (map f).toArray` — a push-fold is the array of the mapped list. -/
theorem foldl_push_eq {α β} (f : α → β) : ∀ (l : List α) (acc : Array β),
    List.foldl (fun b a => b.push (f a)) acc l = acc ++ (l.map f).toArray := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons hd tl ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons, Array.push_eq_append, Array.append_assoc,
        ← List.toArray_cons]

/-- Indexing a `range'` push-fold: `(foldl (·.push (f ·)) #[] [0..n))[i]! = f i` for `i < n`. -/
theorem foldl_push_getElem {β} [Inhabited β] (f : Nat → β) (n i : Nat) (hi : i < n) :
    (List.foldl (fun b a => b.push (f a)) (#[] : Array β) (List.range' 0 n 1))[i]! = f i := by
  rw [foldl_push_eq, Array.empty_append, List.getElem!_toArray, List.getElem!_eq_getElem?_getD]
  simp [hi]

/-- The do-block's sampled `y` (η1=2) with the threaded `(n, y)` state (`n` = fst, array = snd). -/
def encYSt (r : List UInt8) : Nat × Array Poly :=
  List.foldl (fun b _ => (b.1 + 1, b.2.push (samplePolyCBD 2 (prf 2 r b.1)))) (0, #[])
    (List.range' 0 paramK 1)

/-- `y = SamplePolyCBD_η1(PRF(r, 0..k))`. -/
def encY (r : List UInt8) : Array Poly := (encYSt r).2

/-- The `e1` sampling loop, threading the counter `n` from after the `y` loop (`(e1, n)` state). -/
def encE1St (r : List UInt8) : Array Poly × Nat :=
  List.foldl (fun b _ => (b.1.push (samplePolyCBD 2 (prf 2 r b.2)), b.2 + 1)) (#[], (encYSt r).1)
    (List.range' 0 paramK 1)

/-- `e1 = SamplePolyCBD_η2(PRF(r, k..2k))`. -/
def encE1 (r : List UInt8) : Array Poly := (encE1St r).1

/-- `e2 = SamplePolyCBD_η2(PRF(r, 2k))`. -/
def encE2 (r : List UInt8) : Poly := samplePolyCBD 2 (prf 2 r (encE1St r).2)

/-- `ŷ[j] = NTT(y[j])` (the do-block's `ŷ`-building push-loop). -/
def encYHat (r : List UInt8) : Array Poly :=
  List.foldl (fun b a => b.push (ntt (encY r)[a]!)) #[] (List.range' 0 paramK 1)

/-- `Â = ExpandA(ρ)` (the NTT-domain matrix; `Â[i][j]` at index `i·k+j`). -/
def encAHat (ek : List UInt8) : Array Poly := expandMatrix (ekDecode ek).2

/-- `t̂ = ekDecode ek` (the NTT-domain public vector). -/
def encTHat (ek : List UInt8) : Array Poly := (ekDecode ek).1

/-- `μ = Decompress₁(ByteDecode₁(m))` — the spec's message-carrier `Δ·m`. -/
def encMu (m : List UInt8) : Poly := decompressPoly 1 (byteDecode 1 m)

/-- The K-PKE.Encrypt `u`-row accumulator `Σⱼ Âᵀ[i][j] ∘ ŷ[j] = Σⱼ Â[j·k+i] ∘ ŷ[j]` (the nested inner loop). -/
def encUFold (ek r : List UInt8) (i : Nat) : Poly :=
  List.foldl (fun acc j => addPoly acc (pointwiseNtt (encAHat ek)[j * paramK + i]! (encYHat r)[j]!))
    zeroPoly (List.range' 0 paramK 1)

/-- The K-PKE.Encrypt `v` accumulator `Σᵢ t̂[i] ∘ ŷ[i]`. -/
def encVFold (ek r : List UInt8) : Poly :=
  List.foldl (fun acc i => addPoly acc (pointwiseNtt (encTHat ek)[i]! (encYHat r)[i]!))
    zeroPoly (List.range' 0 paramK 1)

/-- The `u` array: `u[i] = NTT⁻¹(encUFold i) + e1[i]` (the outer matmul push-loop). -/
def encUArr (ek r : List UInt8) : Array Poly :=
  List.foldl (fun b i => b.push (addPoly (intt (encUFold ek r i)) (encE1 r)[i]!)) #[]
    (List.range' 0 paramK 1)

/-- The `v` output: `v = NTT⁻¹(encVFold) + e2 + μ`. -/
def encV (ek m r : List UInt8) : Poly :=
  addPoly (addPoly (intt (encVFold ek r)) (encE2 r)) (encMu m)

/-- **THE DO-BLOCK UNFOLD.** `MlKemDecaps.kpkeEncrypt`'s literal `Id.run do` (the `y`/`e1`/`e2`/`ŷ` sampling
loops, the nested `for i for j` matmul for `u`, the `v` matmul) reduces to `ctEncode (encUArr, encV)` — the
`List.foldl` accumulator shapes `encrypt_{u,v}_ring_faithful` consume, the nested matmul a `List.foldl` of
`List.foldl`. Pure monadic-loop plumbing (`forIn_eq_forIn_range'` / opaque-`f` fold), no `native_decide`. -/
theorem kpkeEncrypt_unfold (ek m r : List UInt8) :
    kpkeEncrypt ek m r = ctEncode (encUArr ek r, encV ek m r) := by
  unfold kpkeEncrypt encUArr encV encUFold encVFold encAHat encTHat encYHat encY encE1 encE2
    encE1St encYSt encMu
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

/-- `ŷ[j] = NTT(y[j])` for `j < k` — automatic from `encYHat`'s push-fold (no honest-key hypothesis needed). -/
theorem encYHat_getElem (r : List UInt8) (j : Nat) (hj : j < paramK) :
    (encYHat r)[j]! = ntt (encY r)[j]! := by
  unfold encYHat
  exact foldl_push_getElem (fun a => ntt (encY r)[a]!) paramK j hj

/-- `u[i] = NTT⁻¹(encUFold i) + e1[i]` for `i < k` — extracting the `u`-array row from its push-fold. -/
theorem encUArr_getElem (ek r : List UInt8) (i : Nat) (hi : i < paramK) :
    (encUArr ek r)[i]! = addPoly (intt (encUFold ek r i)) (encE1 r)[i]! := by
  unfold encUArr
  exact foldl_push_getElem (fun i => addPoly (intt (encUFold ek r i)) (encE1 r)[i]!) paramK i hi

/-- **The `u`-row reindex** — on the honest key (`Âᵀ[i][j] = Â[j·k+i] = NTT(A_ji)`), the do-block's index-fold
`encUFold i` equals `encrypt_u_ring_faithful`'s pair-fold over `terms = [(A_0i, y_0), …]` (`List.foldl_map` +
the honest-key `foldl_ext_mem`, with `ŷ[j] = NTT(y_j)` discharged by `encYHat_getElem`). -/
theorem encUFold_eq_terms (ek r : List UInt8) (i : Nat) (A : Nat → Poly)
    (hA : ∀ j, j < paramK → (encAHat ek)[j * paramK + i]! = ntt (A j)) :
    encUFold ek r i
      = List.foldl (fun az t => addPoly az (pointwiseNtt (ntt t.1) (ntt t.2))) zeroPoly
          ((List.range' 0 paramK 1).map (fun j => (A j, (encY r)[j]!))) := by
  unfold encUFold
  rw [List.foldl_map]
  refine foldl_ext_mem _ _ _ (fun acc j hj => ?_) zeroPoly
  have hj' : j < paramK := by have := List.mem_range'.mp hj; omega
  rw [hA j hj', encYHat_getElem r j hj']

/-- **The `v` reindex** — on the honest key (`t̂[i] = NTT(t_i)`), `encVFold` equals `encrypt_v_ring_faithful`'s
pair-fold over `terms = [(t_0, y_0), …]`. -/
theorem encVFold_eq_terms (ek r : List UInt8) (t : Nat → Poly)
    (hT : ∀ i, i < paramK → (encTHat ek)[i]! = ntt (t i)) :
    encVFold ek r
      = List.foldl (fun az s => addPoly az (pointwiseNtt (ntt s.1) (ntt s.2))) zeroPoly
          ((List.range' 0 paramK 1).map (fun i => (t i, (encY r)[i]!))) := by
  unfold encVFold
  rw [List.foldl_map]
  refine foldl_ext_mem _ _ _ (fun acc i hi => ?_) zeroPoly
  have hi' : i < paramK := by have := List.mem_range'.mp hi; omega
  rw [hT i hi', encYHat_getElem r i hi']

/-- **`encryptU_eq_spec` — the byte-level K-PKE.Encrypt `u`-row `=spec`.** Under the honest-key hypothesis
(`Âᵀ[i][j] = NTT(A_ji)`) and size well-formedness, the `R_q` element `u[i] = NTT⁻¹(Σⱼ Âᵀ[i][j] ∘ ŷ[j]) + e1[i]`
that `kpkeEncrypt` feeds to `Compress`/`ctEncode` maps under `toRqKem` to the FIPS 203 K-PKE.Encrypt expression
`(Aᵀ·y)[i] + e1[i] = Σⱼ toRqKem A_ji · toRqKem y_j + toRqKem e1[i]` over `R_q = ℤ_q[X]/(X²⁵⁶+1)`. Composes
`encUArr_getElem` + `encUFold_eq_terms` (the do-block reindex) with `encrypt_u_ring_faithful` (the closed ring
identity off `mlkem_ntt_ring_faithful`). -/
theorem encryptU_eq_spec (ek r : List UInt8) (i : Nat) (hi : i < paramK) (A : Nat → Poly)
    (hA : ∀ j, j < paramK → (encAHat ek)[j * paramK + i]! = ntt (A j))
    (hAsz : ∀ j, j < paramK → (A j).size = 256)
    (hysz : ∀ j, j < paramK → ((encY r)[j]!).size = 256) :
    toRqKem (encUArr ek r)[i]!
      = ((List.range' 0 paramK 1).map (fun j => toRqKem (A j) * toRqKem (encY r)[j]!)).sum
        + toRqKem (encE1 r)[i]! := by
  have hterm : ∀ s ∈ (List.range' 0 paramK 1).map (fun j => (A j, (encY r)[j]!)),
      s.1.size = 256 ∧ s.2.size = 256 := by
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    have hj' : j < paramK := by have := List.mem_range'.mp hj; omega
    exact ⟨hAsz j hj', hysz j hj'⟩
  rw [encUArr_getElem ek r i hi, encUFold_eq_terms ek r i A hA,
      encrypt_u_ring_faithful (encE1 r)[i]! _ hterm, List.map_map]
  rfl

/-- **`encryptV_eq_spec` — the byte-level K-PKE.Encrypt `v` `=spec`.** Under the honest-key hypothesis
(`t̂[i] = NTT(t_i)`) and size well-formedness, the `R_q` element `v = NTT⁻¹(Σᵢ t̂[i] ∘ ŷ[i]) + e2 + μ` maps under
`toRqKem` to the FIPS 203 K-PKE.Encrypt expression `tᵀ·y + e2 + Δ·m = Σᵢ toRqKem t_i · toRqKem y_i + toRqKem e2
+ toRqKem μ` over `R_q` (`μ = Decompress₁(ByteDecode₁(m))` the spec's `Δ·m`, a named `MlKemCorrect` residual).
Composes `encVFold_eq_terms` with `encrypt_v_ring_faithful`. -/
theorem encryptV_eq_spec (ek m r : List UInt8) (t : Nat → Poly)
    (hT : ∀ i, i < paramK → (encTHat ek)[i]! = ntt (t i))
    (htsz : ∀ i, i < paramK → (t i).size = 256)
    (hysz : ∀ i, i < paramK → ((encY r)[i]!).size = 256) :
    toRqKem (encV ek m r)
      = ((List.range' 0 paramK 1).map (fun i => toRqKem (t i) * toRqKem (encY r)[i]!)).sum
        + toRqKem (encE2 r) + toRqKem (encMu m) := by
  have hterm : ∀ s ∈ (List.range' 0 paramK 1).map (fun i => (t i, (encY r)[i]!)),
      s.1.size = 256 ∧ s.2.size = 256 := by
    intro s hs
    rw [List.mem_map] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    have hi' : i < paramK := by have := List.mem_range'.mp hi; omega
    exact ⟨htsz i hi', hysz i hi'⟩
  unfold encV
  rw [encVFold_eq_terms ek r t hT, encrypt_v_ring_faithful (encE2 r) (encMu m) _ hterm, List.map_map]
  rfl

/-- **`kpkeEncrypt_eq_spec` — the byte-level ENCAPS lift, packaged** (the KEM analog of
`DecapsCoreSpec.kpkeDecrypt_eq_spec`). On an honest encapsulation key, `kpkeEncrypt`'s output is exactly
`ctEncode(Compress(u), Compress(v))` of the `R_q` elements `u[i]`, `v` that ARE the FIPS 203 K-PKE.Encrypt
expressions `Σⱼ A_ji·y_j + e1[i]` and `Σᵢ t_i·y_i + e2 + μ`. The only remaining steps to the ciphertext bytes are
`Compress`/`ctEncode` (the `MlKemCorrect` rounding); the ring→ciphertext ALGEBRA is closed here. -/
theorem kpkeEncrypt_eq_spec (ek m r : List UInt8) (A : Nat → Nat → Poly) (t : Nat → Poly)
    (hA : ∀ i, i < paramK → ∀ j, j < paramK → (encAHat ek)[j * paramK + i]! = ntt (A i j))
    (hT : ∀ i, i < paramK → (encTHat ek)[i]! = ntt (t i))
    (hAsz : ∀ i j, (A i j).size = 256) (htsz : ∀ i, (t i).size = 256)
    (hysz : ∀ j, j < paramK → ((encY r)[j]!).size = 256) :
    kpkeEncrypt ek m r = ctEncode (encUArr ek r, encV ek m r)
    ∧ (∀ i, i < paramK →
        toRqKem (encUArr ek r)[i]!
          = ((List.range' 0 paramK 1).map (fun j => toRqKem (A i j) * toRqKem (encY r)[j]!)).sum
            + toRqKem (encE1 r)[i]!)
    ∧ toRqKem (encV ek m r)
        = ((List.range' 0 paramK 1).map (fun i => toRqKem (t i) * toRqKem (encY r)[i]!)).sum
          + toRqKem (encE2 r) + toRqKem (encMu m) :=
  ⟨kpkeEncrypt_unfold ek m r,
   fun i hi => encryptU_eq_spec ek r i hi (A i) (hA i hi) (fun j _ => hAsz i j) hysz,
   encryptV_eq_spec ek m r t hT (fun i _ => htsz i) hysz⟩

#assert_axioms foldl_push_eq
#assert_axioms foldl_push_getElem
#assert_axioms kpkeEncrypt_unfold
#assert_axioms encUFold_eq_terms
#assert_axioms encVFold_eq_terms
#assert_axioms encryptU_eq_spec
#assert_axioms encryptV_eq_spec
#assert_axioms kpkeEncrypt_eq_spec

/-! ### NON-VACUITY — the byte-level `v` lift fires on a GENUINE honest key (`t̂ᵢ = NTT(sampleA)`).

The honest-key hypothesis `t̂[i] = NTT(t_i)` is SATISFIABLE, not vacuous: encode `NTT(sampleA)` (coeffs `< q`)
with `ByteEncode₁₂`, `paramK` times, into a `paramK·384`-byte `t̂` field, append a 32-byte `ρ`; then `ekDecode`'s
`ByteDecode₁₂` recovers it exactly. So `encryptV_eq_spec` fires with `t_i = sampleA` and its `R_q` spec is the
genuine product term `Σ_{i<3} toRqKem sampleA · toRqKem y_i + e2 + μ`, not `_ + 0`. -/

/-- A witness honest `ek`: `ByteEncode₁₂(NTT(sampleA))` repeated `paramK` times, then 32 zero `ρ`-bytes. -/
def witEk : List UInt8 :=
  byteEncode dCoeff (ntt sampleA) ++ byteEncode dCoeff (ntt sampleA)
    ++ byteEncode dCoeff (ntt sampleA) ++ List.replicate 32 (0 : UInt8)

/-- A fixed concrete `r`/`m` witness (the pinned `mFixed`), so the sampled `y`/`e2`/`μ` are computable. -/
def witR : List UInt8 := MlKemEncaps.mFixed.toList

/-- **Non-vacuity**: the witness honest `ek` genuinely satisfies `t̂[i] = ekDecode(witEk).1[i] = NTT(sampleA)`
for every `i < paramK` — the codec round-trips `ByteEncode₁₂/ByteDecode₁₂` on the real NTT-domain value. -/
theorem witEk_hT : ∀ i, i < paramK → (encTHat witEk)[i]! = ntt sampleA := by
  intro i hi
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp only [paramK] at hi; omega
  rcases hi3 with h | h | h <;> subst h <;> native_decide

/-- The concrete `y = SamplePolyCBD(PRF(witR,·))` rows are size 256 (computed on the pinned `witR`). -/
theorem encY_witR_size : ∀ j, j < paramK → ((encY witR)[j]!).size = 256 := by
  intro j hj
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [paramK] at hj; omega
  rcases hj3 with h | h | h <;> subst h <;> native_decide

/-- **Non-vacuity (end-to-end firing)** — `encryptV_eq_spec` FIRES on the witness honest key `witEk`
(`t̂ᵢ = NTT(sampleA)`) and the pinned `witR`: the `R_q` element `v` IS
`Σ_{i<3} toRqKem sampleA · toRqKem y_i + e2 + μ`, a genuine non-degenerate `R_q` product (`toRqKem sampleA ≠ 0`),
not `_ + 0`. The honest-key and size hypotheses discharge by concrete codec computation. -/
theorem encryptV_eq_spec_witness :
    toRqKem (encV witEk witR witR)
      = ((List.range' 0 paramK 1).map (fun i => toRqKem sampleA * toRqKem (encY witR)[i]!)).sum
        + toRqKem (encE2 witR) + toRqKem (encMu witR) :=
  encryptV_eq_spec witEk witR witR (fun _ => sampleA) witEk_hT (fun _ _ => DecapsCoreSpec.sampleA_size) encY_witR_size

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
