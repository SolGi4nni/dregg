/-
# Pki.AcmeEs256 — the ES256 account-key lane for ACME

`Pki.Acme` already models both account-key kinds (`AccountKey.ed25519`,
`AccountKey.p256`), both JWS algorithms (`AcmeAlg.eddsa`, `.es256`), the
protected-header encoding, and the signing input — and it proves the Ed25519
sign/verify round-trip (`jws_sign_verify`). What it does not have is an ES256
*signer*, because the Ed25519 lane was the one wired.

That matters for real interop: **Let's Encrypt (Boulder) does not accept EdDSA
account keys** — RFC 8555 §6.2 leaves the algorithm set to CA policy, and
Boulder's is RSA and ECDSA (P-256/P-384). Pebble follows Boulder. So an account
that a real CA will register must be `ES256`, and the certificate key must
likewise be ECDSA or RSA. This module supplies the ES256 lane over the same
HACL* P-256 the TLS CertificateVerify signer uses.

## JOSE vs TLS signature form

The two wire forms differ, and getting this wrong is a silent 400 from the CA:

* **TLS** (RFC 8446 §4.2.3) carries a DER `ECDSA-Sig-Value ::= SEQUENCE { r, s }`
  — that is `TlsCrypto.Sig.ecdsaP256Sign`.
* **JOSE** (RFC 7518 §3.4) carries the **raw** fixed-width `R ‖ S`, 64 bytes, no
  DER — that is `TlsCrypto.Sig.ecdsaP256SignRaw` used directly.

So this module deliberately does *not* route through `ecdsaP256Sign`; it reuses
the same F*-verified primitive and the same deterministic RFC-6979-spirit nonce
chain, and stops before the DER step.
-/
import Pki.Acme
import TlsCrypto.Sig
import TlsCrypto.P256

namespace Pki.AcmeEs256

open Pki.Acme

/-- Sign an ACME JWS request with a P-256 account key (32-byte scalar), in the
JOSE `ES256` wire form: the raw 64-byte `R ‖ S` over the JWS signing input.
Walks the same deterministic nonce chain as the TLS signer. -/
def signAcmeEs256 (priv : ByteArray) (req : JwsRequest) : Option ByteArray :=
  let msg := signingInput req
  (List.range 8).firstM fun i =>
    TlsCrypto.Sig.ecdsaP256SignRaw priv (TlsCrypto.Sig.nonceAt priv msg i) msg

/-- **What the ES256 signature covers.** Whenever a signature is produced, it is
a P-256 signature over exactly `signingInput req` — the ASCII
`base64url(protected) ‖ "." ‖ base64url(payload)`. Since `encodeHeader` places
the `nonce`, the `url`, and the key identification inside `protected`
(`Pki.Acme.encodeHeader`), the signature binds all three: a captured signature
cannot be replayed against a different URL or a different nonce, and cannot be
re-attributed to a different account.

Non-vacuous: the hypothesis is that signing succeeded, the conclusion names the
message actually signed and is a distinct fact from it. -/
theorem es256_signs_the_signing_input (priv : ByteArray) (req : JwsRequest)
    (sig : ByteArray) (h : signAcmeEs256 priv req = some sig) :
    ∃ i, TlsCrypto.Sig.ecdsaP256SignRaw priv
            (TlsCrypto.Sig.nonceAt priv (signingInput req) i) (signingInput req)
          = some sig := by
  unfold signAcmeEs256 at h
  simp only [List.firstM] at h
  -- `firstM` over a finite list succeeds only at some element of that list
  revert h
  generalize (List.range 8) = is
  induction is with
  | nil => intro h; simp [List.firstM] at h
  | cons i rest ih =>
    intro h
    simp only [List.firstM, Option.orElse_eq_orElse, Option.orElse] at h
    cases hi : TlsCrypto.Sig.ecdsaP256SignRaw priv
        (TlsCrypto.Sig.nonceAt priv (signingInput req) i) (signingInput req) with
    | some s => rw [hi] at h; simp at h; exact ⟨i, by rw [hi, h]⟩
    | none => rw [hi] at h; simp at h; exact ih h

/-- The account key (JWK coordinates) for a P-256 signing scalar: the SEC1
uncompressed point `04 ‖ X ‖ Y` from HACL*, split into the two 32-byte
coordinates RFC 7638 hashes for the thumbprint. `none` if the scalar is out of
range (Hacl_P256 validates it) or the point is not the expected width. -/
def accountKeyOfScalar (priv : ByteArray) : Option AccountKey :=
  match TlsCrypto.P256.pub priv with
  | none => none
  | some pt =>
      let l := pt.toList
      if l.length = 65 then some (.p256 ((l.drop 1).take 32) (l.drop 33)) else none

/-- The SEC1 uncompressed point itself, for the CSR's `SubjectPublicKeyInfo`. -/
def publicPoint (priv : ByteArray) : Option (List UInt8) :=
  (TlsCrypto.P256.pub priv).map ByteArray.toList

/-- Both JWK coordinates are exactly 32 bytes — the width RFC 7518 §6.2.1.2
requires (base64url of a fixed-length coordinate, no leading-zero stripping).
A CA rejects a thumbprint computed over short coordinates, and the thumbprint is
what the HTTP-01 key authorization is built from, so this width is what makes the
challenge answer verify. -/
theorem accountKey_coord_widths (priv : ByteArray) (k : AccountKey)
    (h : accountKeyOfScalar priv = some k) :
    ∃ x y, k = .p256 x y ∧ x.length = 32 ∧ y.length = 32 := by
  unfold accountKeyOfScalar at h
  cases hp : TlsCrypto.P256.pub priv with
  | none => rw [hp] at h; simp at h
  | some pt =>
    rw [hp] at h
    by_cases hl : pt.toList.length = 65
    · simp only [hl, if_true] at h
      refine ⟨(pt.toList.drop 1).take 32, pt.toList.drop 33, (Option.some.inj h).symm, ?_, ?_⟩
      · simp [List.length_take, hl]
      · simp [List.length_drop, hl]
    · simp only [hl, if_false] at h
      exact absurd h (by simp)

end Pki.AcmeEs256
