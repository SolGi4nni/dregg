/-
# TlsCrypto.Sig — the RFC 8446 §9.1 MUST-support certificate signature schemes

RFC 8446 §9.1 requires a TLS 1.3 implementation to support
`rsa_pss_rsae_sha256` (0x0804) and `ecdsa_secp256r1_sha256` (0x0403) for
CertificateVerify, alongside the Ed25519 scheme the core already signs with.
This module binds the two through HACL* (`Hacl_P256_ecdsa_sign_p256_sha2`,
`Hacl_RSAPSS_rsapss_skey_sign` — F*-verified: memory-safe, functionally
correct against their specs, secret-independent) via `ffi/tls_p256_shim.c`,
the same trusted-crossing pattern as `TlsCrypto.P256`.

The handshake core (`TlsHandshake`) does NOT import this module: each
servable certificate carries its signer as a function seam
(`TlsHandshake.CertEntry.sign`), which the executables that link the shim
instantiate with `ecdsaP256Signer` / `rsaPssSigner`. Everything else keeps
its link line.

Wire forms:

* ECDSA (RFC 8446 §4.2.3): the signature TLS carries is a DER-encoded
  `ECDSA-Sig-Value ::= SEQUENCE { r INTEGER, s INTEGER }`. HACL* produces the
  raw 64-byte `R ‖ S`; `derSig` performs the DER encoding (minimal-length
  INTEGERs, leading `0x00` when the high bit is set).
* The ECDSA nonce is derived deterministically from the key and message
  (SHA-256 chain, retried on the negligible out-of-range case) in the spirit
  of RFC 6979 — a repeated nonce reveals the key, so no per-signature
  randomness is trusted to a caller.
* RSA-PSS (RFC 8446 §4.2.3): salt length = digest length (32).
-/
import TlsCrypto

namespace TlsCrypto.Sig

open Crypto

/-- Raw ECDSA-P256-SHA256: the 64-byte `R ‖ S` over `msg` for a 32-byte
scalar `priv` and 32-byte nonce. `none` if either is outside `(0, order)`
(Hacl_P256 validates both). -/
@[extern "drorb_p256_ecdsa_sign"]
opaque ecdsaP256SignRaw (priv nonce msg : ByteArray) : Option ByteArray

/-- RSASSA-PSS with SHA-256 over big-endian `n`/`e`/`d` and the given salt;
the signature is `ceil(modBits/8)` bytes. `none` on an invalid key. -/
@[extern "drorb_rsapss_sha256_sign"]
opaque rsaPssSha256SignRaw (n e d salt msg : ByteArray) : Option ByteArray

/-! ## DER `ECDSA-Sig-Value` encoding -/

/-- A DER INTEGER from an unsigned big-endian byte string: strip leading
zeros (keeping one zero byte for the value 0), then prepend `0x00` when the
top bit is set (DER INTEGERs are signed). -/
def derInt (b : List UInt8) : List UInt8 :=
  let stripped := b.dropWhile (· == 0)
  let v := if stripped.isEmpty then [0] else stripped
  let v := if v.headD 0 ≥ 0x80 then 0x00 :: v else v
  0x02 :: UInt8.ofNat v.length :: v

/-- The DER `ECDSA-Sig-Value` of a raw 64-byte `R ‖ S` signature:
`SEQUENCE { r INTEGER, s INTEGER }`. (Both INTEGERs of a P-256 signature fit
in short-form lengths: ≤ 33 bytes each, sequence ≤ 70.) -/
def derSig (raw : ByteArray) : ByteArray :=
  let l := raw.toList
  let body := derInt (l.take 32) ++ derInt (l.drop 32)
  ByteArray.mk (0x30 :: UInt8.ofNat body.length :: body).toArray

/-! ## The deterministic ECDSA nonce chain

`nonceAt priv msg i` is the `i`-th candidate nonce, an SHA-256 of the
secret key, the message hash, and the retry counter; `ecdsaP256Sign` walks
the chain until Hacl_P256 accepts (a candidate is rejected only when it
falls outside `(0, order)` — probability ≈ 2⁻³², twice never ≈ 2⁻⁶⁴). The
nonce is a pure function of (key, message): the same message never sees two
different nonces under one key, which is the actual requirement. -/
def nonceAt (priv msg : ByteArray) (i : Nat) : ByteArray :=
  sha256 (priv ++ sha256 msg ++ ByteArray.mk #[UInt8.ofNat i])

/-- ECDSA-P256-SHA256 in the TLS wire form: raw sign under the deterministic
nonce chain (up to 8 candidates), then DER-encode. `none` only if every
candidate was out of range (≈ 2⁻²⁵⁶) or the key itself is invalid. -/
def ecdsaP256Sign (priv msg : ByteArray) : Option ByteArray :=
  (List.range 8).firstM (fun i => ecdsaP256SignRaw priv (nonceAt priv msg i) msg)
    |>.map derSig

/-- An RSA private key for the PSS signer seam: big-endian modulus, public
exponent, private exponent. -/
structure RsaKey where
  n : ByteArray
  e : ByteArray
  d : ByteArray

/-- RSA-PSS-SHA256 in the TLS wire form. RFC 8446 §4.2.3: salt length equals
the digest length; the salt is derived deterministically from the key and
message (PSS is secure for any salt, including a fixed one — determinism
here buys reproducibility, not security). -/
def rsaPssSign (key : RsaKey) (msg : ByteArray) : Option ByteArray :=
  rsaPssSha256SignRaw key.n key.e key.d (sha256 (key.d ++ sha256 msg)) msg

end TlsCrypto.Sig
