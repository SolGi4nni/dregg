/*
 * crypto_shim.c — the C side of the crypto FFI seam.
 *
 * This file is the ONLY native code behind `Crypto.lean`. Every function here
 * is a TRUSTED crossing: the Lean core cannot inspect it, and reasons about it
 * only through the axioms declared in `Crypto.lean`. Keep this shim small,
 * boring, and a thin adapter over a FORMALLY VERIFIED library — it is where the
 * formal guarantees change hands (from Lean's proofs to HACL*'s F* proofs), not
 * where they stop.
 *
 * Backend: HACL* / EverCrypt (Project Everest), the machine-checked crypto
 * verified in F* for memory-safety, functional-correctness-against-spec, and
 * secret-independence (constant-time), then extracted to C by KaRaMeL. The
 * primitives this shim calls carry those proofs upstream; the axioms in
 * Crypto.lean are their functional shadows, DISCHARGED by HACL*, not merely
 * assumed of an unverified blob. See CRYPTO-FFI-README.md for the trust ledger.
 *
 * The extracted C comes from the HACL* / EverCrypt distribution's
 * gcc-compatible build (linked as libevercrypt.a); its runtime headers ship
 * under the corresponding karamel/include directory. On non-x86_64 targets
 * the Vale assembly does not apply, so Curve25519 runs the portable
 * Curve25519_51 field arithmetic. ChaCha20-Poly1305 is verified on every
 * target and is this seam's preferred AEAD.
 *
 * AES-GCM is Vale-x86 only, so the verified path reports UnsupportedAlgorithm on
 * hosts without AES-NI+CLMUL (e.g. arm64). Because RFC 9001 §5.2 MANDATES
 * AES-128-GCM for QUIC Initial packets, the AES-GCM crossings here DISPATCH:
 * they call the verified EverCrypt path first, and only when it returns
 * UnsupportedAlgorithm do they fall back to a portable, well-audited backend
 * (aws-lc-rs / AWS-LC, linked as libaes_fallback.a). That fallback is NOT part
 * of the machine-checked TCB — a functional-usability concession so AES-only
 * clients interoperate off-x86. See CRYPTO-FFI-README.md for the trust ledger.
 *
 * ABI convention (all functions):
 *   - ByteArray arguments arrive as borrowed `b_lean_obj_arg`; read with
 *     lean_sarray_cptr / lean_sarray_size, do NOT free.
 *   - `Option ByteArray` results: `none` = lean_box(0); `some x` = a tag-1
 *     constructor with the owned ByteArray in field 0.
 *   - `Bool` results are returned as uint8_t 0/1.
 *   - Size mismatches (wrong key/nonce/tag length) return `none` — they never
 *     read out of bounds. Authentication failure also returns `none`; the two
 *     are indistinguishable to the caller by design.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>                 /* free() for the RSA-PSS public-key handle */

#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "EverCrypt_Curve25519.h"
#include "EverCrypt_Ed25519.h"
#include "EverCrypt_HKDF.h"
#include "EverCrypt_Hash.h"
#include "EverCrypt_Error.h"
#include "Hacl_Spec.h"              /* Spec_Agile_AEAD_* algorithm ids */
#include "Hacl_Streaming_Types.h"  /* Spec_Hash_Definitions_* ids */
#include "Hacl_NaCl.h"             /* crypto_box (X25519 + XSalsa20-Poly1305) */
#include "Hacl_P256.h"             /* ECDSA-P256 verify (server-cert auth) */
#include "Hacl_RSAPSS.h"           /* RSA-PSS verify (server-cert auth) */
#include "Hacl_Hash_Blake2s.h"    /* BLAKE2s (the Noise/ts2021 handshake hash) */
#include "Hacl_HMAC.h"            /* HMAC-BLAKE2s (the Noise HKDF ratchet) */

/* Fixed sizes (bytes) this seam enforces. */
#define DRORB_AEAD_KEY   32u
#define DRORB_AEAD_NONCE 12u
#define DRORB_AEAD_TAG   16u
#define DRORB_X25519_LEN 32u
#define DRORB_ED_PK      32u
#define DRORB_ED_SK      32u  /* RFC 8032 §5.1.5 private key = 32-byte seed */
#define DRORB_ED_SIG     64u
#define DRORB_SHA256_LEN 32u
#define DRORB_BLAKE2S_LEN 32u  /* BLAKE2s-256 digest = the Noise HASHLEN */
#define DRORB_SHA384_LEN 48u
#define DRORB_HKDF_PRK   32u  /* HKDF-SHA256 PRK = HashLen */

/* EverCrypt's agile dispatch reads a CPU-feature table populated by
 * AutoConfig2_init(). Run it once, before main, while single-threaded. On this
 * arm64 host it simply records "no Vale"; it is required for the Hash/AEAD
 * agile entry points to select a valid implementation. */
__attribute__((constructor))
static void drorb_crypto_init(void) {
    EverCrypt_AutoConfig2_init();
}

/* ---- small helpers ---------------------------------------------------- */

static inline lean_object *drorb_none(void) { return lean_box(0); }

static inline lean_object *drorb_some(lean_object *ba) {
    lean_object *s = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(s, 0, ba);
    return s;
}

/* Allocate an owned ByteArray of `n` bytes; caller fills lean_sarray_cptr. */
static inline lean_object *drorb_new_ba(size_t n) {
    return lean_alloc_sarray(1, n, n);
}

/* ---- AEAD: agile seal/open over EverCrypt_AEAD_{en,de}crypt_expand -----
 *
 * The `_expand` one-shot entry points fold key expansion into the call, so no
 * `EverCrypt_AEAD_state_s` handle is allocated or freed here — the shim holds
 * no long-lived secret state. EverCrypt keeps cipher and tag in separate
 * buffers; the Lean interface hands back `ct ‖ tag`, so we place the 16-byte
 * tag immediately after the ciphertext (seal) and split it back off (open).
 */

/* ChaCha20-Poly1305 seal: key(32) nonce(12) ad msg -> Option (ct ‖ tag). */
LEAN_EXPORT lean_obj_res drorb_chachapoly_seal(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg msg) {
    if (lean_sarray_size(key)   != DRORB_AEAD_KEY)   return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t mlen = lean_sarray_size(msg);
    lean_object *out = drorb_new_ba(mlen + DRORB_AEAD_TAG);
    uint8_t *cp = lean_sarray_cptr(out);
    EverCrypt_Error_error_code rc = EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
        lean_sarray_cptr(key),
        lean_sarray_cptr(nonce), DRORB_AEAD_NONCE,
        lean_sarray_cptr(ad), (uint32_t) lean_sarray_size(ad),
        lean_sarray_cptr(msg), (uint32_t) mlen,
        cp,                 /* ciphertext: mlen bytes */
        cp + mlen);         /* tag: 16 bytes, appended */
    if (rc != EverCrypt_Error_Success) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* ChaCha20-Poly1305 open: key(32) nonce(12) ad (ct ‖ tag) -> Option msg. */
LEAN_EXPORT lean_obj_res drorb_chachapoly_open(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg ct) {
    if (lean_sarray_size(key)   != DRORB_AEAD_KEY)   return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t clen = lean_sarray_size(ct);
    if (clen < DRORB_AEAD_TAG) return drorb_none();
    size_t mlen = clen - DRORB_AEAD_TAG;
    uint8_t *cp = lean_sarray_cptr(ct);
    lean_object *out = drorb_new_ba(mlen);
    EverCrypt_Error_error_code rc = EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
        lean_sarray_cptr(key),
        lean_sarray_cptr(nonce), DRORB_AEAD_NONCE,
        lean_sarray_cptr(ad), (uint32_t) lean_sarray_size(ad),
        cp, (uint32_t) mlen,   /* ciphertext without tag */
        cp + mlen,             /* tag: last 16 bytes */
        lean_sarray_cptr(out));
    if (rc != EverCrypt_Error_Success) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* Portable AES-GCM fallback (crates/aes-fallback, aws-lc-rs / AWS-LC), reached
 * only when the verified EverCrypt/Vale path returns UnsupportedAlgorithm. Both
 * write/consume the `ct ‖ tag` layout the shim uses; return 0 on success,
 * nonzero on a bad size or (open) authentication failure. NOT part of the
 * verified TCB — see the header comment and CRYPTO-FFI-README.md. */
extern int32_t drorb_aes_fallback_seal(
        const uint8_t *key, size_t key_len,
        const uint8_t *nonce, size_t nonce_len,
        const uint8_t *ad, size_t ad_len,
        const uint8_t *msg, size_t msg_len,
        uint8_t *out);
extern int32_t drorb_aes_fallback_open(
        const uint8_t *key, size_t key_len,
        const uint8_t *nonce, size_t nonce_len,
        const uint8_t *ad, size_t ad_len,
        const uint8_t *ct, size_t ct_len,
        uint8_t *out);
/* AES-ECB single 16-byte block (crates/aes-fallback): the QUIC header-protection
 * primitive for the AES suites (RFC 9001 §5.4.3, `mask = AES-ECB(hp_key,
 * sample)`). Writes 16 bytes to `out`; 0 on success. NOT part of the verified TCB. */
extern int32_t drorb_aes_ecb_fallback(
        const uint8_t *key, size_t key_len,
        const uint8_t *block, size_t block_len,
        uint8_t *out);

/* AES-GCM seal. The key length selects the cipher: 16 = AES-128-GCM, 32 =
 * AES-256-GCM (RFC 9001 §5.2 QUIC Initials use AES-128-GCM). Dispatch: call the
 * verified EverCrypt/Vale path first (its checked `_expand` entry point does a
 * dynamic hardware probe); if that reports UnsupportedAlgorithm — no AES-NI+CLMUL,
 * e.g. this arm64 host — fall back to the portable aws-lc-rs backend so AES-only
 * peers still interoperate. `none` only on a bad size or a backend error. */
LEAN_EXPORT lean_obj_res drorb_aesgcm_seal(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg msg) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)                  return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t mlen = lean_sarray_size(msg);
    size_t alen = lean_sarray_size(ad);
    lean_object *out = drorb_new_ba(mlen + DRORB_AEAD_TAG);
    uint8_t *cp = lean_sarray_cptr(out);
    uint8_t *kp = lean_sarray_cptr(key);
    uint8_t *np = lean_sarray_cptr(nonce);
    uint8_t *adp = lean_sarray_cptr(ad);
    uint8_t *mp = lean_sarray_cptr(msg);

    EverCrypt_Error_error_code rc = (klen == 16u)
        ? EverCrypt_AEAD_encrypt_expand_aes128_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, mp, (uint32_t) mlen, cp, cp + mlen)
        : EverCrypt_AEAD_encrypt_expand_aes256_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, mp, (uint32_t) mlen, cp, cp + mlen);
    if (rc == EverCrypt_Error_Success) return drorb_some(out);
    if (rc == EverCrypt_Error_UnsupportedAlgorithm) {
        /* Portable fallback: writes `ct ‖ tag` directly into `out`. */
        if (drorb_aes_fallback_seal(kp, klen, np, DRORB_AEAD_NONCE,
                                    adp, alen, mp, mlen, cp) == 0)
            return drorb_some(out);
    }
    lean_dec_ref(out); return drorb_none();
}

/* AES-GCM open. Key length selects the cipher (16/32). Same dispatch as seal:
 * verified EverCrypt first, portable aws-lc-rs fallback on UnsupportedAlgorithm.
 * `none` on auth failure, bad size, or a backend error. */
LEAN_EXPORT lean_obj_res drorb_aesgcm_open(
        b_lean_obj_arg key, b_lean_obj_arg nonce,
        b_lean_obj_arg ad, b_lean_obj_arg ct) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)                  return drorb_none();
    if (lean_sarray_size(nonce) != DRORB_AEAD_NONCE) return drorb_none();
    size_t clen = lean_sarray_size(ct);
    if (clen < DRORB_AEAD_TAG) return drorb_none();
    size_t mlen = clen - DRORB_AEAD_TAG;
    size_t alen = lean_sarray_size(ad);
    uint8_t *cp = lean_sarray_cptr(ct);
    uint8_t *kp = lean_sarray_cptr(key);
    uint8_t *np = lean_sarray_cptr(nonce);
    uint8_t *adp = lean_sarray_cptr(ad);
    lean_object *out = drorb_new_ba(mlen);
    uint8_t *op = lean_sarray_cptr(out);

    EverCrypt_Error_error_code rc = (klen == 16u)
        ? EverCrypt_AEAD_decrypt_expand_aes128_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, cp, (uint32_t) mlen, cp + mlen, op)
        : EverCrypt_AEAD_decrypt_expand_aes256_gcm(
            kp, np, DRORB_AEAD_NONCE, adp, (uint32_t) alen, cp, (uint32_t) mlen, cp + mlen, op);
    if (rc == EverCrypt_Error_Success) return drorb_some(out);
    if (rc == EverCrypt_Error_UnsupportedAlgorithm) {
        /* Portable fallback: verifies the tag, writes plaintext into `out`. */
        if (drorb_aes_fallback_open(kp, klen, np, DRORB_AEAD_NONCE,
                                    adp, alen, cp, clen, op) == 0)
            return drorb_some(out);
    }
    lean_dec_ref(out); return drorb_none();
}

/* AES-ECB single block — QUIC header protection for the AES cipher suites
 * (RFC 9001 §5.4.3): the 5-byte header-protection mask is the first bytes of
 * `AES-ECB(hp_key, sample)`, where `sample` is a 16-byte slice of the protected
 * payload. This is a raw one-block AES permutation (no mode, no IV, no padding).
 *
 * The verified EverCrypt/Vale AES is x86-only and exposes no agile single-block
 * ECB entry point, so — as with AES-GCM off-x86 — this crossing goes straight to
 * the portable aws-lc-rs backend (crates/aes-fallback). The key length selects
 * the cipher (16 = AES-128, 32 = AES-256; QUIC Initials use AES-128). `none` on a
 * bad key/block size or a backend error. NOT part of the machine-checked TCB —
 * header protection carries no confidentiality obligation (its security is the
 * AEAD's); see CRYPTO-FFI-README.md.
 *
 *   drorb_aes_ecb_block : key(16|32) block(16) -> Option (AES-ECB block, 16 bytes)
 */
#define DRORB_AES_BLOCK 16u
LEAN_EXPORT lean_obj_res drorb_aes_ecb_block(
        b_lean_obj_arg key, b_lean_obj_arg block) {
    size_t klen = lean_sarray_size(key);
    if (klen != 16u && klen != 32u)            return drorb_none();
    if (lean_sarray_size(block) != DRORB_AES_BLOCK) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_AES_BLOCK);
    if (drorb_aes_ecb_fallback(lean_sarray_cptr(key), klen,
                               lean_sarray_cptr(block), DRORB_AES_BLOCK,
                               lean_sarray_cptr(out)) == 0)
        return drorb_some(out);
    lean_dec_ref(out); return drorb_none();
}

/* ---- HKDF-SHA256 ------------------------------------------------------ */

/* extract: salt ikm -> prk(32) ; total (EverCrypt_HKDF_extract cannot fail). */
LEAN_EXPORT lean_obj_res drorb_hkdf_sha256_extract(
        b_lean_obj_arg salt, b_lean_obj_arg ikm) {
    lean_object *prk = drorb_new_ba(DRORB_HKDF_PRK);
    EverCrypt_HKDF_extract(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(prk),
        lean_sarray_cptr(salt), (uint32_t) lean_sarray_size(salt),
        lean_sarray_cptr(ikm), (uint32_t) lean_sarray_size(ikm));
    return drorb_some(prk);
}

/* expand: prk(32) info len -> Option okm(len) ; none if len > 255*32. */
LEAN_EXPORT lean_obj_res drorb_hkdf_sha256_expand(
        b_lean_obj_arg prk, b_lean_obj_arg info, size_t len) {
    if (lean_sarray_size(prk) != DRORB_HKDF_PRK) return drorb_none();
    if (len > 255u * 32u) return drorb_none(); /* HKDF max = 255 * HashLen(=32) */
    lean_object *okm = drorb_new_ba(len);
    EverCrypt_HKDF_expand(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(okm),
        lean_sarray_cptr(prk), DRORB_HKDF_PRK,
        lean_sarray_cptr(info), (uint32_t) lean_sarray_size(info),
        (uint32_t) len);
    return drorb_some(okm);
}

/* ---- X25519 (Curve25519 ECDH) ---------------------------------------- */

/* x25519: scalar(32) point(32) -> Option shared(32) ; none on the all-zero
 * low-order-point result (EverCrypt_Curve25519_ecdh returns false), per
 * RFC 7748 §6.1 contributory-behaviour check. */
LEAN_EXPORT lean_obj_res drorb_x25519(
        b_lean_obj_arg scalar, b_lean_obj_arg point) {
    if (lean_sarray_size(scalar) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(point)  != DRORB_X25519_LEN) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_X25519_LEN);
    bool ok = EverCrypt_Curve25519_ecdh(
        lean_sarray_cptr(out), lean_sarray_cptr(scalar), lean_sarray_cptr(point));
    if (!ok) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* x25519Base: scalar(32) -> Option pub(32). secret_to_public is total. */
LEAN_EXPORT lean_obj_res drorb_x25519_base(b_lean_obj_arg scalar) {
    if (lean_sarray_size(scalar) != DRORB_X25519_LEN) return drorb_none();
    lean_object *out = drorb_new_ba(DRORB_X25519_LEN);
    EverCrypt_Curve25519_secret_to_public(
        lean_sarray_cptr(out), lean_sarray_cptr(scalar));
    return drorb_some(out);
}

/* ---- Ed25519 --------------------------------------------------------- */

/* verify: pub(32) msg sig(64) -> Bool. */
LEAN_EXPORT uint8_t drorb_ed25519_verify(
        b_lean_obj_arg pub, b_lean_obj_arg msg, b_lean_obj_arg sig) {
    if (lean_sarray_size(pub) != DRORB_ED_PK)  return 0;
    if (lean_sarray_size(sig) != DRORB_ED_SIG) return 0;
    bool ok = EverCrypt_Ed25519_verify(
        lean_sarray_cptr(pub),
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg),
        lean_sarray_cptr(sig));
    return ok ? 1 : 0;
}

/* sign: privateKey(32, RFC 8032 seed) msg -> Option sig(64). Present so the
 * sign/verify roundtrip axiom is statable; the engine's data path only ever
 * calls verify. EverCrypt derives the public key from the seed internally. */
LEAN_EXPORT lean_obj_res drorb_ed25519_sign(
        b_lean_obj_arg sk, b_lean_obj_arg msg) {
    if (lean_sarray_size(sk) != DRORB_ED_SK) return drorb_none();
    lean_object *sig = drorb_new_ba(DRORB_ED_SIG);
    EverCrypt_Ed25519_sign(
        lean_sarray_cptr(sig),
        lean_sarray_cptr(sk),
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg));
    return drorb_some(sig);
}

/* ---- Server-certificate signature verification (P-256 / RSA-PSS) --------
 *
 * The verified TLS *client* (TlsClient.lean) authenticates a server whose leaf
 * certificate is signed under ecdsa_secp256r1_sha256 or rsa_pss_rsae_sha256
 * (RFC 8446 §4.2.3 / §9.1 MUST-support schemes) — and the same two primitives
 * verify each link's signature when the path is built to a trust root. Both are
 * HACL* (Hacl_P256 / Hacl_RSAPSS), F*-verified for memory safety, functional
 * correctness against their specs, and secret independence, extracted to C by
 * KaRaMeL — the SAME trust ledger as everything above (they live in
 * libevercrypt.a, so no extra link input). These are the VERIFY duals of the
 * sign shims in tls_p256_shim.c; the axioms are in Crypto.lean.
 *
 * Both HACL* entry points hash the message internally (SHA2-256), so the caller
 * passes the raw signed content (the RFC 8446 §4.4.3 CertificateVerify content,
 * or a to-be-signed certificate body) — never a pre-computed digest. */

/* uint8 drorb_p256_ecdsa_verify(pub(64 = X‖Y), msg, sig(64 = R‖S))
 *   ECDSA-P256-SHA256 verify (SignatureScheme ecdsa_secp256r1_sha256). The
 *   public key is the raw 64-byte X‖Y (the caller strips the SEC1 0x04 prefix);
 *   the signature is raw R(32)‖S(32) (the caller decodes the DER ECDSA-Sig-Value
 *   to raw). Returns 1 iff valid, 0 on a bad size or a failed check. Hacl_P256
 *   validates the public key is on-curve, non-infinity. */
LEAN_EXPORT uint8_t drorb_p256_ecdsa_verify(
        b_lean_obj_arg pub, b_lean_obj_arg msg, b_lean_obj_arg sig) {
    if (lean_sarray_size(pub) != 64u) return 0;
    if (lean_sarray_size(sig) != 64u) return 0;
    uint8_t *s = lean_sarray_cptr(sig);
    bool ok = Hacl_P256_ecdsa_verif_p256_sha2(
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg),
        lean_sarray_cptr(pub),
        s,          /* signature_r: first 32 bytes */
        s + 32u);   /* signature_s: last 32 bytes */
    return ok ? 1 : 0;
}

/* The bit length of a big-endian big integer (0 for the empty/zero string). */
static uint32_t crypto_shim_bits(const uint8_t *b, size_t len) {
    size_t i = 0;
    while (i < len && b[i] == 0) i++;
    if (i == len) return 0;
    uint32_t bits = (uint32_t)((len - i - 1) * 8);
    uint8_t top = b[i];
    while (top) { bits++; top >>= 1; }
    return bits;
}

/* uint8 drorb_rsapss_sha256_verify(n, e, sig, msg)
 *   RSASSA-PSS-SHA256 verify (SignatureScheme rsa_pss_rsae_sha256), salt length
 *   = digest length = 32 (RFC 8446 §4.2.3). `n`/`e` are the big-endian modulus
 *   and public exponent extracted from the certificate's SubjectPublicKeyInfo;
 *   `sig` is the raw signature (ceil(modBits/8) bytes); `msg` is the raw signed
 *   content. Returns 1 iff valid, 0 on a bad key shape / size or a failed check.
 *   Hacl_RSAPSS_new_rsapss_load_pkey heap-allocates the public key; freed here. */
#define DRORB_RSA_SALT 32u
LEAN_EXPORT uint8_t drorb_rsapss_sha256_verify(
        b_lean_obj_arg n, b_lean_obj_arg e,
        b_lean_obj_arg sig, b_lean_obj_arg msg) {
    uint32_t modBits = crypto_shim_bits(lean_sarray_cptr(n), lean_sarray_size(n));
    uint32_t eBits   = crypto_shim_bits(lean_sarray_cptr(e), lean_sarray_size(e));
    if (modBits < 256u || modBits > 8192u || eBits == 0) return 0;
    size_t nbytes = (modBits + 7) / 8;
    size_t ebytes = (eBits + 7) / 8;
    if (lean_sarray_size(n) < nbytes || lean_sarray_size(e) < ebytes) return 0;
    /* Hacl_RSAPSS reads exactly ceil(bits/8) bytes of each component; skip any
     * leading zero bytes so the pointers line up with the bit counts. */
    const uint8_t *nb = lean_sarray_cptr(n) + (lean_sarray_size(n) - nbytes);
    const uint8_t *eb = lean_sarray_cptr(e) + (lean_sarray_size(e) - ebytes);
    uint64_t *pkey = Hacl_RSAPSS_new_rsapss_load_pkey(
        modBits, eBits, (uint8_t *) nb, (uint8_t *) eb);
    if (pkey == NULL) return 0;
    bool ok = Hacl_RSAPSS_rsapss_verify(
        Spec_Hash_Definitions_SHA2_256, modBits, eBits, pkey,
        DRORB_RSA_SALT,
        (uint32_t) lean_sarray_size(sig), lean_sarray_cptr(sig),
        (uint32_t) lean_sarray_size(msg), lean_sarray_cptr(msg));
    free(pkey);
    return ok ? 1 : 0;
}

/* ---- RSASSA-PKCS1-v1_5-SHA256 verify (sha256WithRSAEncryption) ----------
 *
 * HACL* / EverCrypt ships RSA-PSS ONLY — but `sha256WithRSAEncryption` (PKCS#1
 * v1.5, OID 1.2.840.113549.1.1.11) is the padding MOST real RSA CA chains sign
 * with, including Let's Encrypt's RSA intermediates (R10/R11) and ISRG Root X1.
 * So the verified TLS client's X.509 path builder reaches a portable, AUDITED
 * aws-lc backend for a PKCS#1 v1.5 link, exactly as the AES-GCM crossings reach
 * aws-lc off-x86. `drorb_rsa_fallback_pkcs1_sha256_verify` is defined in the
 * aes-fallback Rust crate (crates/aes-fallback, linked as libaes_fallback.a) over
 * `aws_lc_rs::signature::RsaPublicKeyComponents::verify` with
 * `RSA_PKCS1_2048_8192_SHA256` — aws-lc's `EVP_DigestVerify` in the
 * `aws_lc_0_42_0` namespace, NOT openssl. It strips any DER `0x00` sign octet and
 * fails CLOSED on a bad key shape / out-of-range modulus / failed check.
 *
 * This is an AUDITED primitive, NOT part of the machine-checked (F*) TCB — the
 * same trust status as the AES-GCM fallback. The `Crypto.lean` axiom naming it
 * (`rsaPkcs1Verify_authentic`) is discharged by aws-lc's audit, not an F* proof,
 * and is labeled as such. See CRYPTO-FFI-README.md for the trust ledger. */
extern uint8_t drorb_rsa_fallback_pkcs1_sha256_verify(
    const uint8_t *n, size_t n_len,
    const uint8_t *e, size_t e_len,
    const uint8_t *sig, size_t sig_len,
    const uint8_t *msg, size_t msg_len);

/* uint8 drorb_rsa_pkcs1_sha256_verify(n, e, sig, msg)
 *   RSASSA-PKCS1-v1_5-SHA256 verify. `n`/`e` are the big-endian modulus and
 *   public exponent from the certificate's SubjectPublicKeyInfo (a leading DER
 *   `0x00` sign octet is tolerated — the Rust backend strips it); `sig` is the
 *   raw signature; `msg` is the raw signed content (the TBSCertificate — aws-lc
 *   hashes it with SHA-256 internally). Returns 1 iff valid, 0 on a bad key
 *   shape / size or a failed check (fail-CLOSED). Backed by audited aws-lc via
 *   the aes-fallback crate — the AUDITED (not F*-verified) dual of the RSA-PSS
 *   crossing above. */
LEAN_EXPORT uint8_t drorb_rsa_pkcs1_sha256_verify(
        b_lean_obj_arg n, b_lean_obj_arg e,
        b_lean_obj_arg sig, b_lean_obj_arg msg) {
    return drorb_rsa_fallback_pkcs1_sha256_verify(
        lean_sarray_cptr(n),   lean_sarray_size(n),
        lean_sarray_cptr(e),   lean_sarray_size(e),
        lean_sarray_cptr(sig), lean_sarray_size(sig),
        lean_sarray_cptr(msg), lean_sarray_size(msg));
}

/* ---- PBKDF2-HMAC-SHA256 password verification (the basic_auth adaptive KDF) --
 *
 * AWS-LC (NOT openssl, NOT bcrypt): `drorb_pbkdf2_fallback_verify` /
 * `drorb_pbkdf2_fallback_hash` are defined in the aes-fallback Rust crate
 * (crates/aes-fallback, linked as libaes_fallback.a) over `aws_lc_rs::pbkdf2`
 * (AWS-LC `PKCS5_PBKDF2_HMAC`) — the SAME audited backend as the AES-GCM/RSA
 * paths above. The stored format is `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>`:
 * verify re-derives the 32-byte PBKDF2 key of the presented password at the
 * stored iteration count + 16-byte random salt and compares in CONSTANT TIME
 * (`aws_lc_rs::pbkdf2::verify` -> AWS-LC `verify_slices_are_equal`). A real work
 * factor (600 000 HMAC-SHA256 rounds) + a per-hash CSPRNG salt — unlike a bare
 * SHA-256. This CLOSED the prior law exception: the former pure-Rust bcrypt/
 * blowfish (widely-used but NOT-formally-audited) is GONE; the whole boundary is
 * now the audited AWS-LC primitive. NOT part of the machine-checked TCB. The
 * Crypto.lean decl naming it (`pbkdf2Verify`) carries no security axiom the
 * proofs consume — the RFC 7617 `BasicAuth.authenticate` decision is proven over
 * ALL `verify`. See CRYPTO-FFI-README.md. */
extern uint8_t drorb_pbkdf2_fallback_verify(
    const uint8_t *password, size_t password_len,
    const uint8_t *hash, size_t hash_len);
extern size_t drorb_pbkdf2_fallback_hash(
    const uint8_t *password, size_t password_len,
    uint32_t iterations, uint8_t *out, size_t out_cap);

/* uint8 drorb_pbkdf2_verify(pass, hash)
 *   pass = raw presented password bytes; hash = the stored PBKDF2 modular string
 *   as bytes (`pbkdf2_sha256$600000$<salt_hex>$<dk_hex>`). Returns 1 iff pass
 *   verifies against hash, 0 otherwise (wrong password / malformed hash —
 *   fail-CLOSED). */
LEAN_EXPORT uint8_t drorb_pbkdf2_verify(
        b_lean_obj_arg pass, b_lean_obj_arg hash) {
    return drorb_pbkdf2_fallback_verify(
        lean_sarray_cptr(pass), lean_sarray_size(pass),
        lean_sarray_cptr(hash), lean_sarray_size(hash));
}

/* ByteArray drorb_pbkdf2_hash(pass, iterations) : IO ByteArray
 *   Generate a fresh stored hash for `pass` at `iterations` rounds (16-byte
 *   AWS-LC CSPRNG salt, 32-byte derived key), returned as the ASCII bytes of
 *   `pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>`. IO because it draws fresh
 *   randomness. On CSPRNG/format failure returns an empty ByteArray. */
LEAN_EXPORT lean_obj_res drorb_pbkdf2_hash(
        b_lean_obj_arg pass, uint32_t iterations, lean_obj_arg /* world */ w) {
    (void) w;
    uint8_t buf[256];
    size_t n = drorb_pbkdf2_fallback_hash(
        lean_sarray_cptr(pass), lean_sarray_size(pass),
        iterations, buf, sizeof buf);
    lean_object *arr = drorb_new_ba(n);
    if (n) memcpy(lean_sarray_cptr(arr), buf, n);
    return lean_io_result_mk_ok(arr);
}

/* ---- Audited CSPRNG (pre-auth key secret minting) ----------------------
 *
 * AWS-LC (NOT `rand`, NOT openssl): drorb_rand_fallback_bytes is defined in the
 * aes-fallback Rust crate over `aws_lc_rs::rand::fill` — the SAME audited entropy
 * source that seeds the PBKDF2 salt above. The control plane mints pre-auth key
 * secrets (Control.PreAuth) with this. NOT part of the machine-checked TCB. */
extern size_t drorb_rand_fallback_bytes(uint8_t *out, size_t len);

/* ByteArray drorb_rand_bytes(len) : IO ByteArray
 *   `len` cryptographically-secure random bytes from AWS-LC's CSPRNG. IO because
 *   it draws fresh randomness. Fail-CLOSED: on CSPRNG failure returns an EMPTY
 *   ByteArray (a zero-length key, which the pre-auth gate rejects). */
LEAN_EXPORT lean_obj_res drorb_rand_bytes(uint32_t len, lean_obj_arg /* world */ w) {
    (void) w;
    lean_object *arr = drorb_new_ba((size_t) len);
    size_t n = drorb_rand_fallback_bytes(lean_sarray_cptr(arr), (size_t) len);
    if (n != (size_t) len) {
        lean_dec(arr);
        arr = drorb_new_ba(0);
    }
    return lean_io_result_mk_ok(arr);
}

/* ---- ML-DSA-65 (FIPS 204) - the post-quantum hybrid half ---------------
 *
 * NOT HACL/EverCrypt. This crossing marshals the four ByteArrays to raw
 * (ptr,len) and calls dregg via dregg-pq: drorb_pq_ml_dsa_verify is defined in
 * the dataplane Rust crate over dregg_pq::ml_dsa_verify. dregg-pq fails CLOSED
 * on a wrong-length key/signature and, when the Lean-verified core is installed,
 * routes accept/reject through the extracted, PROVED
 * Dregg2.Crypto.MlDsaVerifyReal.verifyCore. ctx is the FIPS 204
 * domain-separation string. Returns 0/1. See Crypto.lean mlDsaVerify. */
extern uint8_t drorb_pq_ml_dsa_verify(
    const uint8_t *pk, size_t pk_len,
    const uint8_t *msg, size_t msg_len,
    const uint8_t *sig, size_t sig_len,
    const uint8_t *ctx, size_t ctx_len);

LEAN_EXPORT uint8_t drorb_ml_dsa_verify(
        b_lean_obj_arg pub, b_lean_obj_arg msg,
        b_lean_obj_arg sig, b_lean_obj_arg ctx) {
    return drorb_pq_ml_dsa_verify(
        lean_sarray_cptr(pub), lean_sarray_size(pub),
        lean_sarray_cptr(msg), lean_sarray_size(msg),
        lean_sarray_cptr(sig), lean_sarray_size(sig),
        lean_sarray_cptr(ctx), lean_sarray_size(ctx));
}

/* ---- ML-KEM-768 (FIPS 203) - the post-quantum hybrid KEX half -----------
 *
 * NOT HACL/EverCrypt. Like the ML-DSA-65 crossing above, these marshal the
 * ByteArrays to raw (ptr,len) and call dregg via dregg-pq: drorb_pq_ml_kem_* are
 * defined in the dataplane Rust crate over dregg_pq::hybrid_kem::ml_kem768_* (the
 * SAME ml-kem v0.2.3 primitive dregg's proven X-Wing uses). Fail-CLOSED on a
 * wrong-length key/ciphertext. See Crypto.lean mlKemEncaps / mlKemDecaps and the
 * Xwing composition. The standalone Lean serve exes link ffi/pq_stub.o for these
 * symbols (fail-closed); the deployed dataplane binary links the real dregg wire. */
extern uint8_t drorb_pq_ml_kem_encaps(
    const uint8_t *ek, size_t ek_len, uint8_t *out);
extern uint8_t drorb_pq_ml_kem_decaps(
    const uint8_t *dk, size_t dk_len,
    const uint8_t *ct, size_t ct_len, uint8_t *out);

/* encaps: ek(1184) -> Option (ct(1088) then ss(32)) = Option ba(1120). */
LEAN_EXPORT lean_obj_res drorb_ml_kem_encaps(b_lean_obj_arg ek) {
    lean_object *out = drorb_new_ba(1120u);
    if (drorb_pq_ml_kem_encaps(
            lean_sarray_cptr(ek), lean_sarray_size(ek),
            lean_sarray_cptr(out))) {
        return drorb_some(out);
    }
    lean_dec_ref(out);
    return drorb_none();
}

/* decaps: dk(2400) ct(1088) -> Option ss(32). A tampered-but-well-formed ct
 * returns some(DIFFERENT implicit-reject secret); a malformed key/ct -> none. */
LEAN_EXPORT lean_obj_res drorb_ml_kem_decaps(
        b_lean_obj_arg dk, b_lean_obj_arg ct) {
    lean_object *out = drorb_new_ba(32u);
    if (drorb_pq_ml_kem_decaps(
            lean_sarray_cptr(dk), lean_sarray_size(dk),
            lean_sarray_cptr(ct), lean_sarray_size(ct),
            lean_sarray_cptr(out))) {
        return drorb_some(out);
    }
    lean_dec_ref(out);
    return drorb_none();
}

/* ---- NaCl crypto_box (X25519 + XSalsa20-Poly1305) --------------------
 *
 * crypto_box is the DERP / DISCO authenticated-public-key box: an ephemeral or
 * static X25519 agreement feeds an XSalsa20-Poly1305 secretbox under a 24-byte
 * nonce. Backend is HACL* NaCl (Hacl_NaCl.{c,h}, part of libevercrypt.a) — the
 * same F*-verified stack as the rest of this shim. Layout is the NaCl "easy"
 * convention: the box is `tag(16) ‖ ciphertext(mlen)`; the 24-byte nonce is NOT
 * part of the box here (the DERP/DISCO wire carries it alongside), matching Go's
 * box.Seal output after its nonce prefix.
 *
 *   drorb_crypto_box_seal : peerPub(32) selfSec(32) nonce(24) msg -> Option box(mlen+16)
 *   drorb_crypto_box_open : peerPub(32) selfSec(32) nonce(24) box -> Option msg
 *
 * The shared key is X25519(selfSec, peerPub), so sealing with (peerPub=B, selfSec=a)
 * and opening with (peerPub=A, selfSec=b) agree whenever A=a·G and B=b·G — the DH
 * box agreement. `none` on a bad key/nonce size or (open) an authentication
 * failure; the two are indistinguishable to the caller by design. */
#define DRORB_BOX_NONCE 24u
#define DRORB_BOX_TAG   16u

LEAN_EXPORT lean_obj_res drorb_crypto_box_seal(
        b_lean_obj_arg peerPub, b_lean_obj_arg selfSec,
        b_lean_obj_arg nonce, b_lean_obj_arg msg) {
    if (lean_sarray_size(peerPub) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(selfSec) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(nonce)   != DRORB_BOX_NONCE)   return drorb_none();
    size_t mlen = lean_sarray_size(msg);
    lean_object *out = drorb_new_ba(mlen + DRORB_BOX_TAG);
    uint32_t rc = Hacl_NaCl_crypto_box_easy(
        lean_sarray_cptr(out),
        lean_sarray_cptr(msg), (uint32_t) mlen,
        lean_sarray_cptr(nonce),
        lean_sarray_cptr(peerPub),
        lean_sarray_cptr(selfSec));
    if (rc != 0u) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

LEAN_EXPORT lean_obj_res drorb_crypto_box_open(
        b_lean_obj_arg peerPub, b_lean_obj_arg selfSec,
        b_lean_obj_arg nonce, b_lean_obj_arg boxct) {
    if (lean_sarray_size(peerPub) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(selfSec) != DRORB_X25519_LEN) return drorb_none();
    if (lean_sarray_size(nonce)   != DRORB_BOX_NONCE)   return drorb_none();
    size_t clen = lean_sarray_size(boxct);
    if (clen < DRORB_BOX_TAG) return drorb_none();
    size_t mlen = clen - DRORB_BOX_TAG;
    lean_object *out = drorb_new_ba(mlen);
    uint32_t rc = Hacl_NaCl_crypto_box_open_easy(
        lean_sarray_cptr(out),
        lean_sarray_cptr(boxct), (uint32_t) clen,
        lean_sarray_cptr(nonce),
        lean_sarray_cptr(peerPub),
        lean_sarray_cptr(selfSec));
    if (rc != 0u) { lean_dec_ref(out); return drorb_none(); }
    return drorb_some(out);
}

/* ---- Hashes ---------------------------------------------------------- */

/* sha256: msg -> digest(32). Agile one-shot; total. */
LEAN_EXPORT lean_obj_res drorb_sha256(b_lean_obj_arg msg) {
    lean_object *out = drorb_new_ba(DRORB_SHA256_LEN);
    EverCrypt_Hash_Incremental_hash(
        Spec_Hash_Definitions_SHA2_256,
        lean_sarray_cptr(out),
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg));
    return out;
}

/* sha384: msg -> digest(48). Same agile one-shot, SHA2_384. */
LEAN_EXPORT lean_obj_res drorb_sha384(b_lean_obj_arg msg) {
    lean_object *out = drorb_new_ba(DRORB_SHA384_LEN);
    EverCrypt_Hash_Incremental_hash(
        Spec_Hash_Definitions_SHA2_384,
        lean_sarray_cptr(out),
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg));
    return out;
}

/* ---------------------------------------------------------------------------
 * BLAKE2s (RFC 7693) and HMAC-BLAKE2s — the Noise/ts2021 handshake hash.
 *
 * `Noise_IK_25519_ChaChaPoly_BLAKE2s` names BLAKE2s (32-byte digest), NOT
 * BLAKE2b. Both entry points below are the audited HACL* scalar code from
 * $HACL_DIST (linked out of libevercrypt.a), so the handshake hash sits on
 * the same audited seam as the AEAD and X25519 rather than on a hand-written
 * Lean implementation anchored only by test vectors.
 * ------------------------------------------------------------------------- */

/* blake2s: (outLen, key, msg) -> digest(outLen).
 * `key` empty = unkeyed BLAKE2s (Noise HASH); a non-empty key is the keyed
 * mode (RFC 7693 §3.3). outLen is clamped to 1..32 — BLAKE2s has no longer
 * digest, and a clamp keeps the FFI total for every Lean-side argument. */
LEAN_EXPORT lean_obj_res drorb_blake2s(uint32_t out_len,
                                       b_lean_obj_arg key,
                                       b_lean_obj_arg msg) {
    uint32_t n = out_len;
    if (n < 1u) n = 1u;
    if (n > DRORB_BLAKE2S_LEN) n = DRORB_BLAKE2S_LEN;
    lean_object *out = drorb_new_ba(n);
    Hacl_Hash_Blake2s_hash_with_key(
        lean_sarray_cptr(out), n,
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg),
        lean_sarray_cptr(key), (uint32_t) lean_sarray_size(key));
    return out;
}

/* hmac_blake2s: (key, msg) -> HMAC-BLAKE2s-256 tag(32).
 * RFC 2104 over BLAKE2s with block size 64; HACL* hashes an over-long key and
 * zero-pads a short one, so this is total in both arguments. This is the
 * primitive the Noise HKDF ratchet (kdf1/kdf2/kdf3) is built from. */
LEAN_EXPORT lean_obj_res drorb_hmac_blake2s(b_lean_obj_arg key,
                                            b_lean_obj_arg msg) {
    lean_object *out = drorb_new_ba(DRORB_BLAKE2S_LEN);
    Hacl_HMAC_compute_blake2s_32(
        lean_sarray_cptr(out),
        lean_sarray_cptr(key), (uint32_t) lean_sarray_size(key),
        lean_sarray_cptr(msg), (uint32_t) lean_sarray_size(msg));
    return out;
}
