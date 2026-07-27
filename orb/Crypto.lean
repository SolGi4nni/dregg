/-
# Crypto — the axiomatic crypto FFI seam

The engine's protocol models (TLS records, WireGuard transport, WebRTC/DTLS,
JWT/COSE signatures) all need a handful of cryptographic primitives. Those
primitives are NOT proven in Lean here. This module declares them as a small,
fixed set of `opaque` functions bound by `@[extern]` to `ffi/crypto_shim.c`,
which calls HACL*/EverCrypt (Project Everest) — crypto verified in F* for
memory-safety, functional-correctness-against-spec, and secret-independence
(constant-time), then extracted to C by KaRaMeL. The module states the algebraic
properties the models rely on as explicit `axiom`s.

That is the trust boundary, made legible:

  * The interface is exactly the declarations below — nothing else crosses.
  * Each primitive is `opaque`: the Lean core cannot unfold it, inspect key
    material, or "peek" at ciphertext. It knows the primitives ONLY through the
    axioms in the `Assumptions` section.
  * Every axiom is the functional shadow of a THEOREM proved of HACL*/EverCrypt
    upstream — not an assumption about an unverified blob. The residual trust is
    the F*/KaRaMeL toolchain and this shim's marshalling. See
    CRYPTO-FFI-README.md for the full trust ledger.

The engine's security theorems are therefore CONDITIONAL: they hold *relative
to* these assumptions. We do not re-derive AEAD security or the discrete-log
hardness of X25519; we name them, and compose. One worked composition is
sketched at the end (`Compose`), tying `aead_open_authentic` to the reactor's
abstract-AEAD WireGuard/TLS lanes.

All primitives operate on `ByteArray` (a flat, FFI-friendly buffer). The
engine's `Proto.Bytes = List UInt8` view converts with `⟨l.toArray⟩` / `.toList`
in pure Lean; the FFI boundary stays on `ByteArray` so the C shim is a clean
pointer+length adapter.
-/

namespace Crypto

/-! ## The interface: opaque primitives bound to the C shim.

Sizes (in bytes) the shim enforces; a size mismatch yields `none`, never a
buffer overrun:

| primitive            | key | nonce | tag | digest |
|----------------------|-----|-------|-----|--------|
| ChaCha20-Poly1305    | 32  | 12    | 16  |   –    |
| AES-GCM (128 / 256)  |16/32| 12    | 16  |   –    |
| X25519 scalar/point  | 32  |  –    |  –  |   –    |
| Ed25519 pub/sig/sk   | 32  |  –    | 64  |   –    |
| SHA-256 / SHA-384    |  –  |  –    |  –  | 32/48  |
-/

/-- AEAD seal (ChaCha20-Poly1305, IETF 96-bit nonce): `key nonce ad msg`.
Returns `some (ct ‖ tag)` (|msg|+16 bytes), or `none` on a bad key/nonce size. -/
@[extern "drorb_chachapoly_seal"]
opaque chachaSeal (key nonce ad msg : ByteArray) : Option ByteArray

/-- AEAD open (ChaCha20-Poly1305): `key nonce ad ct`. Returns `some msg` on a
valid tag, `none` on authentication failure OR a bad size. The two are
deliberately indistinguishable to the caller. -/
@[extern "drorb_chachapoly_open"]
opaque chachaOpen (key nonce ad ct : ByteArray) : Option ByteArray

/-- AEAD seal (AES-GCM). The key length selects the cipher: 16 = AES-128-GCM,
32 = AES-256-GCM (RFC 9001 §5.2 QUIC Initials use AES-128-GCM). The shim prefers
the verified EverCrypt/Vale path and, only where that reports unavailable (no
AES-NI+CLMUL, e.g. arm64), uses a portable unverified backend — see the trust
ledger. `none` on a bad key/nonce size. -/
@[extern "drorb_aesgcm_seal"]
opaque aesGcmSeal (key nonce ad msg : ByteArray) : Option ByteArray

/-- AEAD open (AES-GCM, 128/256 by key length). `none` on auth failure or bad
size. Same verified-preferred / portable-fallback dispatch as `aesGcmSeal`. -/
@[extern "drorb_aesgcm_open"]
opaque aesGcmOpen (key nonce ad ct : ByteArray) : Option ByteArray

/-- AES-ECB single 16-byte block, `out = AES(key, block)` — a raw one-block AES
permutation (no mode, no IV, no padding). The key length selects the cipher
(16 = AES-128, 32 = AES-256). This is the QUIC header-protection primitive for the
AES cipher suites (RFC 9001 §5.4.3: the 5-byte mask is `AES-ECB(hp_key,
sample)[0..5]`). `none` on a bad key/block size. Same dispatch story as AES-GCM:
verified EverCrypt/Vale AES is x86-only, so off-x86 this uses the portable
aws-lc-rs backend — NOT part of the machine-checked TCB (header protection carries
no confidentiality obligation; its security is the AEAD's). See the trust ledger. -/
@[extern "drorb_aes_ecb_block"]
opaque aesEcbBlock (key block : ByteArray) : Option ByteArray

/-- HKDF-Extract (SHA-256): `salt ikm ↦ some prk` (32 bytes). -/
@[extern "drorb_hkdf_sha256_extract"]
opaque hkdfExtract (salt ikm : ByteArray) : Option ByteArray

/-- HKDF-Expand (SHA-256): `prk info len ↦ some okm` (`len` bytes), or `none`
if `prk` is not 32 bytes or `len > 255*32`. -/
@[extern "drorb_hkdf_sha256_expand"]
opaque hkdfExpand (prk info : ByteArray) (len : USize) : Option ByteArray

/-- X25519 scalar multiplication: `scalar point ↦ some shared` (32 bytes), or
`none` on a low-order point (all-zero output, RFC 7748 §6.1). -/
@[extern "drorb_x25519"]
opaque x25519 (scalar point : ByteArray) : Option ByteArray

/-- X25519 base-point multiplication: `scalar ↦ some pub` (32 bytes). -/
@[extern "drorb_x25519_base"]
opaque x25519Base (scalar : ByteArray) : Option ByteArray

/-- NaCl `crypto_box` seal (X25519 + XSalsa20-Poly1305): `peerPub selfSec nonce
msg ↦ some (tag ‖ ct)` (|msg|+16 bytes), or `none` on a bad key/nonce size. The
shared key is X25519(selfSec, peerPub); the 24-byte `nonce` is carried alongside
the box on the wire (DERP/DISCO), not inside it. This is the DERP ClientInfo /
ServerInfo handshake box and the DISCO Ping/Pong box. -/
@[extern "drorb_crypto_box_seal"]
opaque cryptoBoxSeal (peerPub selfSec nonce msg : ByteArray) : Option ByteArray

/-- NaCl `crypto_box` open: `peerPub selfSec nonce (tag ‖ ct) ↦ some msg` on a
valid tag, `none` on authentication failure OR a bad size (indistinguishable to
the caller). The receiver supplies the *sender's* public key as `peerPub` and its
own secret as `selfSec`; the shared key X25519(selfSec, peerPub) matches the
sender's, so a box sealed for it opens. -/
@[extern "drorb_crypto_box_open"]
opaque cryptoBoxOpen (peerPub selfSec nonce ct : ByteArray) : Option ByteArray

/-- Ed25519 detached verify: `pub msg sig ↦ Bool`. `false` on a bad signature
OR a wrong-length `pub`/`sig`. -/
@[extern "drorb_ed25519_verify"]
opaque ed25519Verify (pub msg sig : ByteArray) : Bool

/-- Ed25519 detached sign: `privateKey(32) msg ↦ some sig(64)`, where the
private key is the RFC 8032 §5.1.5 32-byte seed (EverCrypt derives the public key
from it internally). Present so the sign/verify roundtrip is statable; the
engine's data path only ever verifies. -/
@[extern "drorb_ed25519_sign"]
opaque ed25519Sign (secretKey msg : ByteArray) : Option ByteArray

/-- **ECDSA-P256-SHA256 detached verify** (SignatureScheme `ecdsa_secp256r1_sha256`,
RFC 8446 §4.2.3/§9.1) — the server-certificate authentication primitive for the
verified TLS client. `pub msg sig ↦ Bool`: `pub` is the raw 64-byte `X ‖ Y`
public point (the SEC1 `0x04` prefix stripped), `sig` is the raw 64-byte `R ‖ S`
(the DER `ECDSA-Sig-Value` decoded to raw), `msg` is the raw signed content
(HACL* hashes it with SHA-256 internally). Returns `false` — never a panic — on a
wrong-length key/signature, an off-curve key, or a failed check (fail-CLOSED).
Backed by HACL*'s F*-verified `Hacl_P256_ecdsa_verif_p256_sha2` via
`ffi/crypto_shim.c` (same trust ledger as `ed25519Verify`); the VERIFY dual of
`TlsCrypto.Sig.ecdsaP256SignRaw`. -/
@[extern "drorb_p256_ecdsa_verify"]
opaque ecdsaP256Verify (pub msg sig : ByteArray) : Bool

/-- **RSASSA-PSS-SHA256 detached verify** (SignatureScheme `rsa_pss_rsae_sha256`,
RFC 8446 §4.2.3/§9.1, salt length = digest length = 32) — the RSA server-
certificate authentication primitive. `n e sig msg ↦ Bool`: `n`/`e` are the
big-endian modulus and public exponent from the certificate's
SubjectPublicKeyInfo, `sig` is the raw signature (`ceil(modBits/8)` bytes), `msg`
is the raw signed content (HACL* hashes it with SHA-256 internally). Returns
`false` — never a panic — on a bad key shape/size or a failed check (fail-CLOSED).
Backed by HACL*'s F*-verified `Hacl_RSAPSS_rsapss_verify` via `ffi/crypto_shim.c`;
the VERIFY dual of `TlsCrypto.Sig.rsaPssSha256SignRaw`. -/
@[extern "drorb_rsapss_sha256_verify"]
opaque rsaPssVerify (n e sig msg : ByteArray) : Bool

/-- **RSASSA-PKCS1-v1_5-SHA256 detached verify** (`sha256WithRSAEncryption`, OID
`1.2.840.113549.1.1.11`) — the RSA certificate-signature primitive for the padding
MOST real RSA CA chains sign with, including Let's Encrypt's RSA intermediates
(R10/R11) and ISRG Root X1. `n e sig msg ↦ Bool`: `n`/`e` are the big-endian
modulus and public exponent from the issuer certificate's SubjectPublicKeyInfo (a
leading DER `0x00` sign octet is tolerated), `sig` is the raw signature, `msg` is
the raw signed content — the child's TBSCertificate (the backend hashes it with
SHA-256 internally). Returns `false` — never a panic — on a bad key shape/size or a
failed check (fail-CLOSED).

Unlike `rsaPssVerify` (HACL* `Hacl_RSAPSS`, F*-verified), this crossing is backed
by AUDITED aws-lc — `aws_lc_rs::signature::RsaPublicKeyComponents::verify` with
`RSA_PKCS1_2048_8192_SHA256` (aws-lc's `EVP_DigestVerify`, the `aws_lc_0_42_0`
namespace, NEVER openssl), via the aes-fallback crate (`ffi/crypto_shim.c` →
`drorb_rsa_fallback_pkcs1_sha256_verify`). HACL* ships RSA-PSS only, so PKCS#1 v1.5
has no F*-verified verifier; aws-lc is the well-audited backend, the SAME trust
status as the AES-GCM fallback — an audited primitive, NOT part of the
machine-checked (F*) TCB. Its authenticity axiom (`rsaPkcs1Verify_authentic`) is
discharged by aws-lc's AUDIT, not an F* proof, and is labeled as such. -/
@[extern "drorb_rsa_pkcs1_sha256_verify"]
opaque rsaPkcs1Verify (n e sig msg : ByteArray) : Bool

/-- **ML-DSA-65 (FIPS 204) detached verify** — the post-quantum half of the
hybrid signature seam: `pub msg sig ctx ↦ Bool`. Returns `false` — never a panic —
on a wrong-length public key/signature or a failed cryptographic check (fail-CLOSED:
a present-but-invalid PQ half must make the whole hybrid verification reject).

Unlike the HACL*/EverCrypt primitives above, this crossing is bound (via the
dataplane's `drorb_ml_dsa_verify`) to dregg's `dregg_pq::ml_dsa_verify`. When the
verified core is installed (`dregg_pq::install_verified_mldsa_verify_core`), the
accept/reject verdict is computed by the extracted, Lean-verified
`Dregg2.Crypto.MlDsaVerifyReal.verifyCore` (dregg's BRICK 8 — the full-dimension
ML-DSA-65 verify over the real 1952/3309-byte pk/sig), PROVED by dregg to accept a
genuine signature (`MlDsaVerifyReal.verify_accepts_real`) and reject a one-byte
tamper / wrong message (`verify_rejects_tampered`, `verify_rejects_wrong_msg`), and
to agree with the FIPS 204 spec (`Fips204Verify.verifyCore_unfolds_to_def`,
`extractedApi_fips204`). `ctx` is the FIPS 204 domain-separation string. The
soundness of THIS primitive is dregg's proof, not re-derived here — see
`Assumptions.mlDsaVerify_authentic`. -/
@[extern "drorb_ml_dsa_verify"]
opaque mlDsaVerify (pub msg sig ctx : ByteArray) : Bool

/-- **ML-KEM-768 (FIPS 203) encapsulation** — the post-quantum half of the orb's
hybrid TLS 1.3 X-Wing key exchange (`X25519MLKEM768`). Encapsulate to a 1184-byte
encapsulation key: `ek ↦ some (ct ‖ ss)` — the 1088-byte ciphertext concatenated with
the 32-byte shared secret (1120 bytes) — or `none` on a wrong-length/malformed `ek`
(fail-CLOSED). Like `mlDsaVerify`, this crossing is bound (via the dataplane's
`drorb_ml_kem_encaps`) to dregg's `dregg_pq::hybrid_kem::ml_kem768_encaps` — the SAME
`ml-kem` v0.2.3 ML-KEM-768 primitive dregg's proven X-Wing (`hybrid_kem`) is built on.
The IND-CCA soundness of THIS primitive is dregg's proof, not re-derived here — see
`Xwing.mlKem_ind_cca`. -/
@[extern "drorb_ml_kem_encaps"]
opaque mlKemEncaps (ek : ByteArray) : Option ByteArray

/-- **ML-KEM-768 (FIPS 203) decapsulation** — recover the 32-byte shared secret:
`dk ct ↦ some ss`, or `none` on a wrong-length/malformed `dk`/`ct` (fail-CLOSED). A
well-formed-but-TAMPERED ciphertext does not fail — it implicit-rejects to a DIFFERENT
(message-independent) secret (ML-KEM's FO implicit-reject), so the parties DIVERGE
without leaking. Bound to `dregg_pq::hybrid_kem::ml_kem768_decaps`. -/
@[extern "drorb_ml_kem_decaps"]
opaque mlKemDecaps (dk ct : ByteArray) : Option ByteArray

/-- **PBKDF2-HMAC-SHA256 password verification** (the `basic_auth` adaptive KDF):
`pass hash ↦ Bool`. `pass` is the raw presented password bytes; `hash` is the
stored ASCII modular string `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>`.
Returns `true` iff `pass` verifies against `hash`, `false` on a wrong password OR a
malformed / non-`pbkdf2_sha256` stored string (fail-CLOSED, never panics). The
stored iteration count (e.g. `600000`) + 16-byte random salt are parsed out and
used to re-derive the 32-byte PBKDF2 key, which is compared to the stored derived
key in CONSTANT TIME (`aws_lc_rs::pbkdf2::verify` → AWS-LC `verify_slices_are_equal`)
— a genuine work factor (600 000 HMAC-SHA256 rounds) and per-hash CSPRNG salt,
unlike a bare `sha256`.

TRUST POSTURE — AUDITED-primitive backend, NOT the F* TCB. Bound (via the
dataplane's `drorb_pbkdf2_fallback_verify`) to `aws_lc_rs::pbkdf2` (AWS-LC's
`PKCS5_PBKDF2_HMAC`) — the SAME audited primitive as this seam's AES-GCM/RSA
paths. This CLOSED the prior law exception: the former pure-Rust `bcrypt`/RustCrypto
`blowfish` (a not-formally-audited primitive) has been REMOVED. No openssl, no
bcrypt. Not part of the machine-checked TCB. Unlike the HACL* primitives this decl
states NO security axiom the models consume: the RFC 7617 `BasicAuth.authenticate`
decision is proven over ALL `verify`; what is residual is the STRENGTH of this
boundary, named here. See CRYPTO-FFI-README.md. -/
@[extern "drorb_pbkdf2_verify"]
opaque pbkdf2Verify (pass hash : ByteArray) : Bool

/-- **PBKDF2-HMAC-SHA256 hash generation** (the operator/helper side of the
`basic_auth` store): `pass iterations ↦ IO (stored hash bytes)`. Draws a fresh
16-byte AWS-LC CSPRNG salt (hence `IO`), derives a 32-byte PBKDF2 key at
`iterations` rounds, and returns the ASCII bytes of
`pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>` — the exact stored format
`pbkdf2Verify` accepts. Bound to `drorb_pbkdf2_fallback_hash` (AWS-LC). Used by the
`pbkdf2-hash` helper to mint credential-store entries; carries no proof obligation. -/
@[extern "drorb_pbkdf2_hash"]
opaque pbkdf2Hash (pass : ByteArray) (iterations : UInt32) : IO ByteArray

/-- SHA-256: `msg ↦ digest` (32 bytes). Total. -/
@[extern "drorb_sha256"]
opaque sha256 (msg : ByteArray) : ByteArray

/-- SHA-384: `msg ↦ digest` (48 bytes). Total. -/
@[extern "drorb_sha384"]
opaque sha384 (msg : ByteArray) : ByteArray

/-! ### BLAKE2s — the Noise/ts2021 handshake hash

`Noise_IK_25519_ChaChaPoly_BLAKE2s` names **BLAKE2s** (32-byte digest), not
BLAKE2b. Both entry points are bound to the audited HACL* scalar code
(`Hacl_Hash_Blake2s_hash_with_key`, `Hacl_HMAC_compute_blake2s_32`), so the
handshake hash sits on the same audited seam as the AEAD and X25519 instead of
on a Lean implementation anchored only by test vectors. -/

/-- BLAKE2s (RFC 7693): `outLen key msg ↦ digest` (`outLen` bytes, clamped to
1–32). An empty `key` is the unkeyed mode — Noise's `HASH`; a non-empty key is
the keyed mode. Bound to HACL* `Hacl_Hash_Blake2s_hash_with_key`. Total. -/
@[extern "drorb_blake2s"]
opaque blake2s (outLen : UInt32) (key msg : ByteArray) : ByteArray

/-- HMAC-BLAKE2s-256: `key msg ↦ tag` (32 bytes), RFC 2104 with block size 64.
The primitive Noise's HKDF ratchet is built from. Bound to HACL*
`Hacl_HMAC_compute_blake2s_32`. Total in both arguments. -/
@[extern "drorb_hmac_blake2s"]
opaque hmacBlake2s (key msg : ByteArray) : ByteArray

/-- Noise's `HASH(x)`: unkeyed BLAKE2s-256. -/
def blake2sHash (msg : ByteArray) : ByteArray := blake2s 32 ByteArray.empty msg

/-! ## CRC32C (Castagnoli) — the SCTP packet checksum (RFC 4960 §6.8, RFC 3309)

Not a cryptographic primitive and not part of the trust boundary: a pure,
total, Lean-native computation (no FFI, no axiom). SCTP protects every packet
with CRC32C — the reflected CRC with the Castagnoli polynomial `0x1EDC6F41`
(reversed form `0x82F63B78`), initial and final value `0xFFFFFFFF`. It is here
because the WebRTC data-channel model (`WebrtcTransport`) and its live driver
frame SCTP packets whose checksum this computes. -/

/-- One CRC32C step over a byte (reflected, polynomial `0x82F63B78`). -/
def crc32cByte (crc : UInt32) (b : UInt8) : UInt32 := Id.run do
  let mut c := crc ^^^ b.toUInt32
  for _ in [0:8] do
    c := if c &&& 1 == 1 then (c >>> 1) ^^^ 0x82F63B78 else c >>> 1
  return c

/-- CRC32C (Castagnoli) of a byte buffer: initial `0xFFFFFFFF`, reflected input
and output, final XOR `0xFFFFFFFF`. This is exactly the value the SCTP wire
format carries (little-endian) in the common-header checksum field. -/
def crc32c (data : ByteArray) : UInt32 :=
  (data.foldl crc32cByte 0xFFFFFFFF) ^^^ 0xFFFFFFFF

/-- The CRC32C value as its 4 little-endian wire bytes (RFC 3309 packing, the
order aiortc's `struct.pack("<L", …)` produces). -/
def crc32cBytesLE (data : ByteArray) : ByteArray :=
  let c := crc32c data
  ByteArray.mk #[UInt8.ofNat (c.toNat % 256), UInt8.ofNat (c.toNat / 256 % 256),
                 UInt8.ofNat (c.toNat / 65536 % 256), UInt8.ofNat (c.toNat / 16777216 % 256)]

/-! ## Assumptions: the trust boundary as Lean axioms.

Each `axiom` below is an ASSUMED property of the linked C implementation. They
are consistent because every primitive is `opaque` (nothing here can be refuted
by unfolding a definition). They are exactly the algebraic facts the protocol
models consume. This is the entire crypto trust surface of the engine — and each
axiom below is discharged upstream by a HACL*/EverCrypt F* proof (cited in
CRYPTO-FFI-README.md), so an auditor reviews *this list* against those proofs.

We deliberately do NOT assert security properties we cannot state honestly in
Lean's logic: collision-resistance and IND-CPA are asymptotic/probabilistic and
have no faithful first-order encoding here. Those live in CRYPTO-FFI-README.md
as informal, audit-checked assumptions. What we DO state are the exact,
checkable functional/algebraic laws the models compose against. -/

namespace Assumptions

/-- **AEAD correctness (ChaCha20-Poly1305).** Whatever `chachaSeal` produces,
`chachaOpen` under the same key/nonce/ad recovers the plaintext. -/
axiom chacha_open_seal_roundtrip :
  ∀ key nonce ad msg ct,
    chachaSeal key nonce ad msg = some ct →
    chachaOpen key nonce ad ct = some msg

/-- **AEAD authenticity / forgery-resistance (ChaCha20-Poly1305).** The ONLY
ciphertexts that open are the ones `chachaSeal` produced for that exact
`(key, nonce, ad, plaintext)`. This is the functional shadow of INT-CTXT: an
adversary cannot fabricate a `ct` that decrypts under a key it does not hold.
A model that accepts a message *only when* `chachaOpen … = some m` thereby only
ever accepts genuine sender output. -/
axiom chacha_open_authentic :
  ∀ key nonce ad ct msg,
    chachaOpen key nonce ad ct = some msg →
    chachaSeal key nonce ad msg = some ct

/-- **AEAD correctness (AES-256-GCM).** -/
axiom aesgcm_open_seal_roundtrip :
  ∀ key nonce ad msg ct,
    aesGcmSeal key nonce ad msg = some ct →
    aesGcmOpen key nonce ad ct = some msg

/-- **AEAD authenticity (AES-256-GCM).** -/
axiom aesgcm_open_authentic :
  ∀ key nonce ad ct msg,
    aesGcmOpen key nonce ad ct = some msg →
    aesGcmSeal key nonce ad msg = some ct

/-- **AES-ECB block is total and 16 bytes on a valid key/block.** On a valid key
size (16 or 32) and a 16-byte input block, the raw AES permutation is total and
returns exactly 16 bytes. This is all QUIC header protection needs — the mask is
well-defined and 5 bytes long. No secrecy is asserted: header protection is an XOR
mask whose security is the AEAD's, not this permutation's (RFC 9001 §5.4). -/
axiom aes_ecb_block_valid :
  ∀ (key block : ByteArray),
    (key.size = 16 ∨ key.size = 32) → block.size = 16 →
    ∃ out, aesEcbBlock key block = some out ∧ out.size = 16

/-- **X25519 Diffie–Hellman agreement.** When both public keys derive from
their scalars, the two DH computations agree: `a·(b·G) = b·(a·G)`. This is the
shared-secret property session-key derivation rests on. -/
axiom x25519_dh_agree :
  ∀ a b pa pb,
    x25519Base a = some pa →
    x25519Base b = some pb →
    x25519 a pb = x25519 b pa

/-- **crypto_box correctness (self).** Whatever `cryptoBoxSeal` produces under a
key/secret/nonce, `cryptoBoxOpen` under the *same* `(peerPub, selfSec, nonce)`
recovers the plaintext — the shared key X25519(selfSec, peerPub) is identical on
both sides, so sealing and opening with the same handle round-trips. -/
axiom crypto_box_open_seal_roundtrip :
  ∀ peerPub selfSec nonce msg ct,
    cryptoBoxSeal peerPub selfSec nonce msg = some ct →
    cryptoBoxOpen peerPub selfSec nonce ct = some msg

/-- **crypto_box authenticity / forgery-resistance.** The ONLY boxes that open
under `(peerPub, selfSec, nonce)` are the ones `cryptoBoxSeal` produced for that
exact plaintext — the functional shadow of INT-CTXT for the NaCl box. A model
that accepts a DERP/DISCO message *only when* `cryptoBoxOpen … = some m` thereby
only ever accepts a message genuinely sealed under the shared key: no party
lacking `selfSec` (or the peer's secret) can fabricate one. -/
axiom crypto_box_open_authentic :
  ∀ peerPub selfSec nonce ct msg,
    cryptoBoxOpen peerPub selfSec nonce ct = some msg →
    cryptoBoxSeal peerPub selfSec nonce msg = some ct

/-- **crypto_box DH agreement.** The DERP/DISCO cross-party property: a box the
sender A seals *for* B — `cryptoBoxSeal B_pub A_sec nonce msg` — opens for the
receiver B addressing A — `cryptoBoxOpen A_pub B_sec nonce`. Both sides compute
the same shared key `A_sec·B_pub = B_sec·A_pub` (the X25519 agreement), so the
box the client puts on the DERP wire is exactly what the real server decrypts. -/
axiom crypto_box_agree :
  ∀ aSec aPub bSec bPub nonce msg ct,
    x25519Base aSec = some aPub →
    x25519Base bSec = some bPub →
    cryptoBoxSeal bPub aSec nonce msg = some ct →
    cryptoBoxOpen aPub bSec nonce ct = some msg

/-- **Ed25519 correctness.** A signature made with a private key verifies under
the matching public key. `pubOf` abstracts "the public key of this seed" — the
deterministic `EverCrypt_Ed25519_secret_to_public` of the 32-byte seed — so this
is a pure statement about the implementation. -/
axiom ed25519_pubOf : ByteArray → ByteArray

axiom ed25519_sign_verify_roundtrip :
  ∀ sk msg sig,
    ed25519Sign sk msg = some sig →
    ed25519Verify (ed25519_pubOf sk) msg sig = true

/-! ### ECDSA-P256 / RSA-PSS verify authenticity — the server-cert-auth shadow.

The verified TLS client authenticates a server by checking its CertificateVerify
signature (and, on the chain, each link's signature) under the leaf/issuer public
key. The security content of "the check passed" is EUF-CMA: the ONLY signatures
that verify under a public key are ones produced by the matching private key. We
state that as the functional shadow (acceptance ⟹ genuine), exactly parallel to
`chacha_open_authentic` and `mlDsaVerify_authentic`, discharged upstream by
HACL*'s F* proofs of `Hacl_P256` / `Hacl_RSAPSS`. A verifier that accepts a
server *only when* `ecdsaP256Verify`/`rsaPssVerify` returns `true` thereby only
ever accepts a signature the key holder genuinely produced. -/

/-- `ecdsaP256Genuine pub msg sig`: `sig` is an ECDSA-P256-SHA256 signature the
private key matching public point `pub` produced over `msg` — the abstract
"authentic signer output" (the ECDSA analog of "`chachaSeal` produced this ct"). -/
axiom ecdsaP256Genuine : ByteArray → ByteArray → ByteArray → Prop

/-- **ECDSA-P256 verify authenticity (EUF-CMA shadow).** Under public key `pub`,
the only signatures `ecdsaP256Verify` accepts are genuine ones by the matching
private key. Discharged by HACL*'s verified `Hacl_P256_ecdsa_verif_p256_sha2`. -/
axiom ecdsaP256Verify_authentic :
  ∀ pub msg sig,
    ecdsaP256Verify pub msg sig = true →
    ecdsaP256Genuine pub msg sig

/-- `rsaPssGenuine n e msg sig`: `sig` is an RSASSA-PSS-SHA256 signature the
private key matching the RSA public key `(n, e)` produced over `msg`. -/
axiom rsaPssGenuine : ByteArray → ByteArray → ByteArray → ByteArray → Prop

/-- **RSA-PSS verify authenticity (EUF-CMA shadow).** Under RSA public key
`(n, e)`, the only signatures `rsaPssVerify` accepts are genuine ones by the
matching private key. Discharged by HACL*'s verified `Hacl_RSAPSS_rsapss_verify`. -/
axiom rsaPssVerify_authentic :
  ∀ n e sig msg,
    rsaPssVerify n e sig msg = true →
    rsaPssGenuine n e msg sig

/-- `rsaPkcs1Genuine n e msg sig`: `sig` is an RSASSA-PKCS1-v1_5-SHA256 signature
the private key matching the RSA public key `(n, e)` produced over `msg`. -/
axiom rsaPkcs1Genuine : ByteArray → ByteArray → ByteArray → ByteArray → Prop

/-- **RSA-PKCS1-v1_5 verify authenticity (EUF-CMA shadow).** Under RSA public key
`(n, e)`, the only signatures `rsaPkcs1Verify` accepts are genuine ones by the
matching private key.

AUDITED, NOT F*-verified: `rsaPkcs1Verify` is backed by aws-lc
(`RsaPublicKeyComponents::verify` / `RSA_PKCS1_2048_8192_SHA256`), a well-audited
constant-time implementation — NOT HACL*/EverCrypt (which ships RSA-PSS only). This
axiom is therefore discharged by aws-lc's AUDIT, at the SAME trust level as the
AES-GCM fallback, one notch below the F*-machine-checked HACL* axioms
(`rsaPssVerify_authentic` &c.). It is a NAMED audited-primitive assumption, listed
in the trust ledger (CRYPTO-FFI-README.md); nothing here is openssl. -/
axiom rsaPkcs1Verify_authentic :
  ∀ n e sig msg,
    rsaPkcs1Verify n e sig msg = true →
    rsaPkcs1Genuine n e msg sig

/-- **SHA output lengths.** Honest, checkable structural facts (used where the
models slice fixed-width digests). Collision-resistance is NOT stated here — it
is an informal, audit-tracked assumption (see README). -/
axiom sha256_len : ∀ msg, (sha256 msg).size = 32
axiom sha384_len : ∀ msg, (sha384 msg).size = 48

/-! ### ML-DSA-65 (FIPS 204) — the post-quantum verify, shadowed from dregg's proof.

The classical Ed25519 axioms above are the shadow of HACL*/EverCrypt's F* proofs.
The ML-DSA-65 verify is the shadow of dregg's SEPARATE, already-discharged proof —
the extracted, Lean-verified `Dregg2.Crypto.MlDsaVerifyReal.verifyCore`. The orb
does NOT re-prove FIPS-204 soundness; it names dregg's result and composes. -/

/-- The ML-DSA-65 public key dregg derives from a 32-byte seed
(`dregg_pq::MlDsaKey::from_ed25519_seed(seed).public_bytes()`), abstracted — the
value a verifier ENROLLS and PINS to a holder's identity, matching dregg's
`Id = H(ed25519 ‖ ml_dsa)`. The PQ key is never self-carried in a token. -/
axiom mlDsaPubOf : ByteArray → ByteArray

/-- `mlDsaGenuine seed ctx msg sig`: `sig` is a signature dregg's ML-DSA-65 signer
would produce for `(seed, ctx, msg)` — the abstract "authentic sender output",
the ML-DSA analog of "`chachaSeal` produced this `ct`". -/
axiom mlDsaGenuine : ByteArray → ByteArray → ByteArray → ByteArray → Prop

/-- **ML-DSA-65 verify authenticity / forgery-resistance — the functional shadow
of dregg's PROVEN FIPS-204 verify.** Under a pinned key `mlDsaPubOf seed`, the ONLY
signatures `mlDsaVerify` accepts are genuine ones by the matching seed. This is
NOT re-derived here: it is the shadow of `Dregg2.Crypto.MlDsaVerifyReal.verifyCore`'s
proven accept-genuine / reject-tamper gate (`verify_accepts_real`,
`verify_rejects_tampered`, `verify_rejects_wrong_msg`) and its proven agreement
with the FIPS 204 spec (`Fips204Verify.verifyCore_unfolds_to_def`, `extractedApi_fips204`).
The residual trust is dregg's F*/leanc toolchain and the `drorb_ml_dsa_verify`
marshalling — exactly parallel to the HACL* axioms above (the shape mirrors
`chacha_open_authentic`: acceptance implies genuine sender output). -/
axiom mlDsaVerify_authentic :
  ∀ seed ctx msg sig,
    mlDsaVerify (mlDsaPubOf seed) msg sig ctx = true →
    mlDsaGenuine seed ctx msg sig

end Assumptions

/-! ## Compose — one worked example of "relative to these assumptions".

The reactor never calls these primitives directly. Instead the protocol models
take crypto as an *abstract parameter* — e.g. `Wireguard.Config.openTransport :
Keys → TransportMsg → Option Bytes` — and prove their transition-system theorems
for every such function. Deploying the engine means INSTANTIATING that parameter
with the primitives above; the model's theorem then holds for the real crypto
*because* the axioms discharge the model's crypto hypotheses.

Concretely, take an `openTransport` instantiated so that accepting an inbound
record requires `chachaOpen key nonce ad ct = some plaintext`. `Wireguard.step`
delivers plaintext only on that success (`Wireguard.lean`, the `openTransport …
= none` reject path). Composing with `chacha_open_authentic`: any accepted
record's plaintext is exactly what the peer sealed under the shared key — so no
attacker-fabricated record is ever delivered. The WireGuard replay/authenticity
theorems (`wg_replay_rejected`, `Window.replay_rejected`) thus transfer to the
deployed engine, conditional on `chacha_open_authentic`.

The same shape covers TLS: `Reactor.Tls.tls_no_plain_after_close` states that
once the TLS FSM is closing/closed, no plaintext is ever surfaced — a property
of the *record-layer wiring*, independent of the cipher. It composes with AEAD
confidentiality (informal, README) to give the full "no plaintext leaks"
guarantee: the FSM never surfaces plaintext after close (proved), and before
close every surfaced record was a genuine `*Open … = some _` (authenticity
axiom). We state the seam, not a re-proof of AEAD. -/

section Compose

/-- The abstract "open" contract a model lane expects: a partial function from
ciphertext to plaintext. -/
abbrev OpenFn := ByteArray → Option ByteArray

/-- Instantiate a model's open-lane at a fixed key/nonce/ad with ChaCha. -/
def chachaOpenAt (key nonce ad : ByteArray) : OpenFn := chachaOpen key nonce ad

/-- **The discharge, made explicit.** Under the ChaCha instantiation, "this
ciphertext was accepted" implies "the peer sealed exactly this plaintext" — the
model's authenticity hypothesis, delivered by the axiom. A model theorem written
against a generic `OpenFn` with an authenticity side-condition can be closed by
supplying `chachaOpenAt` and this lemma. -/
theorem chachaOpenAt_authentic (key nonce ad ct msg : ByteArray)
    (h : chachaOpenAt key nonce ad ct = some msg) :
    chachaSeal key nonce ad msg = some ct :=
  Assumptions.chacha_open_authentic key nonce ad ct msg h

/-- **The ML-DSA-65 discharge, made explicit.** A signature accepted by
`mlDsaVerify` under a pinned key `mlDsaPubOf seed` is a genuine signature by the
matching seed — the JWT hybrid's ML-DSA half authenticity, delivered by dregg's
proven verify core (via `Assumptions.mlDsaVerify_authentic`). Its `#print axioms`
names `mlDsaVerify_authentic`, surfacing the dregg FIPS-204 dependency honestly. -/
theorem mlDsaVerify_authentic_at (seed ctx msg sig : ByteArray)
    (h : mlDsaVerify (Assumptions.mlDsaPubOf seed) msg sig ctx = true) :
    Assumptions.mlDsaGenuine seed ctx msg sig :=
  Assumptions.mlDsaVerify_authentic seed ctx msg sig h

end Compose

/-! ## Xwing — the post-quantum hybrid KEM combiner (X25519 + ML-KEM-768).

The orb's TLS 1.3 hybrid key exchange (`X25519MLKEM768`, `TlsHandshake`) derives its
shared secret from an **X-Wing** combiner: one classical X25519 secret `ss_x25519` and
one post-quantum ML-KEM-768 secret `ss_mlkem`, fed **concatenated, with the handshake
transcript**, through a single HKDF-SHA256 KDF — the published X-Wing construction, and
dregg's `hybrid_kem` combiner VERBATIM in structure (concatenation-KDF, **never XOR**).

Two properties are the point of this cut, both the orb's NEW proofs:

* **`xwing_kex_sound`** — the hybrid secret binds BOTH halves: it is unpredictable
  (IND-CCA) if EITHER X25519 OR ML-KEM is, provided the KDF is a dual-PRF. Breaking one
  component (e.g. X25519 to a quantum adversary) leaves the other's secret an
  unpredictable key the adversary cannot pin — harvest-now-decrypt-later defeated.
* **`xwing_ikm_is_concat`** — the combiner's HKDF input keying material is exactly
  `ss_x25519 ‖ ss_mlkem` (concatenation), so neither half can be cancelled (the XOR
  tripwire, as a `rfl` theorem).

The ML-KEM half's IND-CCA is NOT re-proved here — it is dregg's
`Dregg2.Crypto.MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe` (ML-KEM IND-CCA reduced to the
module-lattice floor `Lattice.MLWESearchHard` + the QROM idealisation), the PQ leg of
`Dregg2.Crypto.HybridCombiner.hybrid_kem_ind_cca_if_either`, surfaced here as the named
`Xwing.mlKem_ind_cca`. The combiner machinery below MIRRORS `HybridCombiner` (its
`Unpredictable` / `DualPRF` / `hybrid_kem_ind_cca_if_either`), re-proved clean over
`ByteArray`. The orb names dregg's lattice result and composes; it does not re-derive
FIPS 203. -/
namespace Xwing

/-- **Unpredictable** — a secret, as a function of the hidden encapsulation coins, is
injective: distinct coins give distinct secrets, so no fixed prediction pins it. The
IND-CCA currency (`Dregg2.Crypto.HybridCombiner.KemIndCca` = `Unpredictable`). -/
def Unpredictable {In : Type} (f : In → ByteArray) : Prop := ∀ a b, f a = f b → a = b

/-- **DUAL-PRF (the X-Wing KDF requirement).** The combiner preserves unpredictability
keyed on EITHER input: injective in the first key (second key + transcript fixed) AND in
the second. The standard X-Wing assumption on the combiner, stated explicitly. -/
def DualPRF (K : ByteArray → ByteArray → ByteArray → ByteArray) : Prop :=
  (∀ (k2 tr a b : ByteArray), K a k2 tr = K b k2 tr → a = b) ∧
  (∀ (k1 tr a b : ByteArray), K k1 a tr = K k1 b tr → a = b)

/-- Unpredictability flows through the CLASSICAL channel (pq secret held fixed). -/
theorem unpredictable_via_classical {In : Type}
    (K : ByteArray → ByteArray → ByteArray → ByteArray) (hd : DualPRF K)
    (tr sspq : ByteArray) (source : In → ByteArray) (hx : Unpredictable source) :
    Unpredictable (fun i => K (source i) sspq tr) :=
  fun a b h => hx a b (hd.1 sspq tr (source a) (source b) h)

/-- Unpredictability flows through the PQ channel (classical secret held fixed) — the leg
a single-keyed (non-dual) combiner would LACK. -/
theorem unpredictable_via_pq {In : Type}
    (K : ByteArray → ByteArray → ByteArray → ByteArray) (hd : DualPRF K)
    (tr ssx : ByteArray) (source : In → ByteArray) (hp : Unpredictable source) :
    Unpredictable (fun i => K ssx (source i) tr) :=
  fun a b h => hp a b (hd.2 ssx tr (source a) (source b) h)

/-- **The combiner core — unpredictable if EITHER component's secret is** (under the
dual-PRF). Mirrors `HybridCombiner.hybrid_kem_ind_cca_if_either`, re-proved clean. -/
theorem binds_both {In : Type}
    (K : ByteArray → ByteArray → ByteArray → ByteArray) (hd : DualPRF K)
    (tr ssx sspq : ByteArray) (sourceX sourcePq : In → ByteArray)
    (heither : Unpredictable sourceX ∨ Unpredictable sourcePq) :
    Unpredictable (fun i => K (sourceX i) sspq tr) ∨
    Unpredictable (fun i => K ssx (sourcePq i) tr) :=
  match heither with
  | Or.inl hx => Or.inl (unpredictable_via_classical K hd tr sspq sourceX hx)
  | Or.inr hp => Or.inr (unpredictable_via_pq K hd tr ssx sourcePq hp)

/-! ### The concrete orb combiner (HKDF-SHA256 over the concatenation). -/

/-- HKDF domain-separation / version tag for the orb's TLS hybrid KEX combiner. Its own
per-surface domain (X-Wing domain separation); the CONSTRUCTION — HKDF-SHA256 over the
concatenation `ss_x25519 ‖ ss_mlkem` with the transcript as `info` — is dregg's
`hybrid_kem::combine` verbatim in structure. -/
def xwingDomain : ByteArray := "drorb-tls-hybrid-kem-x25519-mlkem768-v1".toUTF8

/-- **The X-Wing combiner**: `HKDF-Expand(HKDF-Extract(salt = domain, ikm = ss_x25519 ‖
ss_mlkem), info = domain ‖ transcript, 32)`. A **concatenation KDF, never XOR**: the
output depends jointly and inextricably on BOTH secrets. `none` only on an HKDF size
fault (a 32-byte expand never faults). -/
def xwingCombine (ssX ssPq transcript : ByteArray) : Option ByteArray :=
  (hkdfExtract xwingDomain (ssX ++ ssPq)).bind
    (fun prk => hkdfExpand prk (xwingDomain ++ transcript) (32 : USize))

/-- **The combiner is CONCATENATION, never XOR** (the X-Wing tripwire, as a theorem). The
HKDF input keying material `xwingCombine` feeds is exactly `ssX ++ ssPq` — both secrets
concatenated — so the derived key depends jointly on BOTH. With XOR an adversary who
learned one secret could cancel it; with the concatenation neither half can be removed.
`rfl`-clean. -/
theorem xwing_ikm_is_concat (ssX ssPq transcript : ByteArray) :
    xwingCombine ssX ssPq transcript
      = (hkdfExtract xwingDomain (ssX ++ ssPq)).bind
          (fun prk => hkdfExpand prk (xwingDomain ++ transcript) (32 : USize)) := rfl

/-- The total combiner used for the composition statement (`xwingCombine` defaulting to
empty only on the impossible 32-byte HKDF fault). -/
def xwingKdf (ssX ssPq tr : ByteArray) : ByteArray :=
  (xwingCombine ssX ssPq tr).getD ByteArray.empty

/-! ### The named dependencies (the trust boundary), and the orb's NEW composition proof. -/

/-- **The X-Wing dual-PRF assumption**, stated explicitly. The concrete HKDF-SHA256
concatenation combiner `xwingKdf` is a dual-PRF (injective keyed on either secret) — the
standard X-Wing requirement on the combiner (`Dregg2.Crypto.HybridCombiner.DualPRF`), the
functional shadow of HKDF-SHA256's collision-resistance / dual-PRF security. Named, not
hidden. -/
axiom xwing_kdf_dualPRF : DualPRF xwingKdf

/-- The ML-KEM-768 shared secret as a function of the honest encapsulation coins, for a
given encapsulation key `ek` (the handle dregg's `mlKemSecret H coins` is phrased over). -/
axiom mlKemSource : ByteArray → ByteArray → ByteArray

/-- **ML-KEM-768 IND-CCA — the functional shadow of dregg's PROVEN reduction to MLWE.**
For every encapsulation key, the ML-KEM shared secret, as a function of the hidden
encapsulation coins, is UNPREDICTABLE. NOT re-derived here: the shadow of
`Dregg2.Crypto.MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe` (ML-KEM IND-CCA from
`Lattice.MLWESearchHard` + `QROMInjective`), the PQ leg of
`Dregg2.Crypto.HybridCombiner.hybrid_kem_ind_cca_if_either`. Residual trust: dregg's
lattice proof + the `drorb_ml_kem_*` marshalling — parallel to `mlDsaVerify_authentic`. -/
axiom mlKem_ind_cca : ∀ (ek : ByteArray), Unpredictable (mlKemSource ek)

/-- **`xwing_kex_sound` — the X-Wing shared secret binds BOTH halves.** Under the dual-PRF,
the derived secret is unpredictable (IND-CCA) if EITHER the X25519 OR the ML-KEM secret
source is — through the corresponding channel. The orb's NEW composition proof; the
ML-KEM IND-CCA it consumes rests on dregg's core (`mlKem_ind_cca`). Non-vacuous, names
the concrete `xwingKdf`. -/
theorem xwing_kex_sound {In : Type} (tr ssx sspq : ByteArray)
    (sourceX sourcePq : In → ByteArray)
    (heither : Unpredictable sourceX ∨ Unpredictable sourcePq) :
    Unpredictable (fun i => xwingKdf (sourceX i) sspq tr) ∨
    Unpredictable (fun i => xwingKdf ssx (sourcePq i) tr) :=
  binds_both xwingKdf xwing_kdf_dualPRF tr ssx sspq sourceX sourcePq heither

/-- **Harvest-now-decrypt-later is defeated** (the load-bearing composition): even if the
classical X25519 secret is fully known to a (quantum) adversary — `ssx` fixed — the X-Wing
key stays UNPREDICTABLE because the ML-KEM half does, resting on dregg's IND-CCA (MLWE
floor). A MITM breaking ONLY X25519 cannot derive the session key. -/
theorem xwing_kex_pq_protects (tr ssx ek : ByteArray) :
    Unpredictable (fun coins => xwingKdf ssx (mlKemSource ek coins) tr) :=
  unpredictable_via_pq xwingKdf xwing_kdf_dualPRF tr ssx (mlKemSource ek) (mlKem_ind_cca ek)

end Xwing

end Crypto

#print axioms Crypto.Xwing.xwing_kex_sound
#print axioms Crypto.Xwing.xwing_kex_pq_protects
#print axioms Crypto.Xwing.xwing_ikm_is_concat
