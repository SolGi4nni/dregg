/*
 * tls_p256_shim.c — secp256r1 (NIST P-256) key exchange AND the certificate
 * signature algorithms of the TLS 1.3 handshake, over HACL*'s verified
 * Hacl_P256 / Hacl_RSAPSS (F*-verified for memory safety, functional
 * correctness against their specs, and secret independence; extracted to C
 * by KaRaMeL — same trust ledger as crypto_shim.c, see CRYPTO-FFI-README.md).
 *
 * RFC 8446 §9.1 makes secp256r1 a MUST-support named group and
 * `ecdsa_secp256r1_sha256` / `rsa_pss_rsae_sha256` MUST-support signature
 * schemes; this shim is the native side of `TlsCrypto.P256` and
 * `TlsCrypto.Sig` and is linked ONLY by the executables that import those
 * modules (the TLS conformance oracle and selftest) — the pure handshake core
 * reaches it through the `ServerParams` key-exchange/signing seams, so
 * nothing else links against these symbols.
 *
 * Wire format (RFC 8446 §4.2.8.2): the KeyShareEntry for secp256r1 is the
 * SEC1 uncompressed point `0x04 ‖ X(32) ‖ Y(32)` (65 octets); the ECDH shared
 * secret is the X coordinate (32 octets, big-endian). Hacl_P256 works on the
 * raw 64-octet `X ‖ Y` form; this shim adds/strips the 0x04 prefix and
 * truncates the shared point to X. ECDSA signatures come back as raw
 * `R(32) ‖ S(32)`; the DER `ECDSA-Sig-Value` encoding TLS carries is done in
 * Lean (`TlsCrypto.Sig.derSig`), keeping this crossing minimal.
 *
 * ABI convention (same as crypto_shim.c): ByteArray arguments arrive borrowed;
 * `Option ByteArray` results are lean_box(0) for `none` or a tag-1 ctor for
 * `some`. Size mismatches and invalid points/scalars/keys return `none`.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <string.h>

#include "Hacl_P256.h"
#include "Hacl_RSAPSS.h"

static inline lean_object *shim_none(void) { return lean_box(0); }

static inline lean_object *shim_some(lean_object *ba) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, ba);
    return o;
}

static inline lean_object *shim_new_ba(size_t n) {
    lean_object *ba = lean_alloc_sarray(1, n, n);
    return ba;
}

/* Option ByteArray drorb_p256_pub(ByteArray priv)
 *   The server's KeyShareEntry key_exchange field: the uncompressed public
 *   point 0x04 ‖ X ‖ Y for a 32-byte scalar. none if the scalar is not in
 *   (0, order). */
LEAN_EXPORT lean_obj_res drorb_p256_pub(b_lean_obj_arg priv) {
    if (lean_sarray_size(priv) != 32u) return shim_none();
    uint8_t pub[64];
    if (!Hacl_P256_dh_initiator(pub, lean_sarray_cptr(priv))) return shim_none();
    lean_object *out = shim_new_ba(65);
    uint8_t *p = lean_sarray_cptr(out);
    p[0] = 0x04;
    memcpy(p + 1, pub, 64);
    return shim_some(out);
}

/* Option ByteArray drorb_p256_ecdh(ByteArray priv, ByteArray peer)
 *   ECDH agreement: peer is the client's 65-byte uncompressed point; the
 *   result is the 32-byte X coordinate of the shared point (RFC 8446 §7.4.2).
 *   none on a malformed/invalid point (Hacl_P256_dh_responder validates the
 *   peer key: on-curve, non-infinity) or an invalid scalar. */
LEAN_EXPORT lean_obj_res drorb_p256_ecdh(b_lean_obj_arg priv, b_lean_obj_arg peer) {
    if (lean_sarray_size(priv) != 32u) return shim_none();
    if (lean_sarray_size(peer) != 65u) return shim_none();
    const uint8_t *pp = lean_sarray_cptr(peer);
    if (pp[0] != 0x04) return shim_none();   /* uncompressed points only */
    uint8_t raw[64];
    memcpy(raw, pp + 1, 64);
    uint8_t shared[64];
    if (!Hacl_P256_dh_responder(shared, raw, lean_sarray_cptr(priv)))
        return shim_none();
    lean_object *out = shim_new_ba(32);
    memcpy(lean_sarray_cptr(out), shared, 32);   /* X coordinate */
    return shim_some(out);
}

/* Option ByteArray drorb_p256_ecdsa_sign(ByteArray priv, ByteArray nonce,
 *                                        ByteArray msg)
 *   ECDSA-P256-SHA256 (SignatureScheme ecdsa_secp256r1_sha256, RFC 8446
 *   §4.2.3): the raw 64-byte `R ‖ S` signature over `msg`, under the 32-byte
 *   scalar `priv` with the 32-byte per-signature `nonce` k. Hacl_P256
 *   validates 0 < priv, nonce < order; `none` when either is out of range.
 *   The caller supplies the nonce (the Lean wrapper derives it
 *   deterministically from the key and message, RFC-6979-style). */
LEAN_EXPORT lean_obj_res drorb_p256_ecdsa_sign(b_lean_obj_arg priv,
                                               b_lean_obj_arg nonce,
                                               b_lean_obj_arg msg) {
    if (lean_sarray_size(priv) != 32u || lean_sarray_size(nonce) != 32u)
        return shim_none();
    uint8_t sig[64];
    if (!Hacl_P256_ecdsa_sign_p256_sha2(sig, (uint32_t)lean_sarray_size(msg),
                                        lean_sarray_cptr(msg),
                                        lean_sarray_cptr(priv),
                                        lean_sarray_cptr(nonce)))
        return shim_none();
    lean_object *out = shim_new_ba(64);
    memcpy(lean_sarray_cptr(out), sig, 64);
    return shim_some(out);
}

/* The bit length of a big-endian big integer (0 for the empty/zero string). */
static uint32_t shim_bits(const uint8_t *b, size_t len) {
    size_t i = 0;
    while (i < len && b[i] == 0) i++;
    if (i == len) return 0;
    uint32_t bits = (uint32_t)((len - i - 1) * 8);
    uint8_t top = b[i];
    while (top) { bits++; top >>= 1; }
    return bits;
}

/* Option ByteArray drorb_rsapss_sha256_sign(ByteArray n, ByteArray e,
 *                                           ByteArray d, ByteArray salt,
 *                                           ByteArray msg)
 *   RSASSA-PSS with SHA-256 (SignatureScheme rsa_pss_rsae_sha256, RFC 8446
 *   §4.2.3): sign `msg` under the RSA secret key given as big-endian
 *   modulus/public-exponent/private-exponent, with the caller's PSS salt
 *   (RFC 8446 §4.2.3 requires salt length = digest length, so the Lean
 *   wrapper passes 32 bytes). The signature is `ceil(modBits/8)` bytes.
 *   `none` on an invalid key shape or a Hacl_RSAPSS rejection. */
LEAN_EXPORT lean_obj_res drorb_rsapss_sha256_sign(b_lean_obj_arg n,
                                                  b_lean_obj_arg e,
                                                  b_lean_obj_arg d,
                                                  b_lean_obj_arg salt,
                                                  b_lean_obj_arg msg) {
    uint32_t modBits = shim_bits(lean_sarray_cptr(n), lean_sarray_size(n));
    uint32_t eBits = shim_bits(lean_sarray_cptr(e), lean_sarray_size(e));
    uint32_t dBits = shim_bits(lean_sarray_cptr(d), lean_sarray_size(d));
    if (modBits < 256u || modBits > 8192u || eBits == 0 || dBits == 0)
        return shim_none();
    /* Hacl_RSAPSS reads exactly ceil(bits/8) bytes of each component; strip
     * any leading zero bytes so the pointers line up with the bit counts. */
    const uint8_t *nb = lean_sarray_cptr(n) + (lean_sarray_size(n) - (modBits + 7) / 8);
    const uint8_t *eb = lean_sarray_cptr(e) + (lean_sarray_size(e) - (eBits + 7) / 8);
    const uint8_t *db = lean_sarray_cptr(d) + (lean_sarray_size(d) - (dBits + 7) / 8);
    size_t sigLen = (modBits + 7) / 8;
    lean_object *out = shim_new_ba(sigLen);
    if (!Hacl_RSAPSS_rsapss_skey_sign(Spec_Hash_Definitions_SHA2_256,
                                      modBits, eBits, dBits,
                                      (uint8_t *)nb, (uint8_t *)eb, (uint8_t *)db,
                                      (uint32_t)lean_sarray_size(salt),
                                      lean_sarray_cptr(salt),
                                      (uint32_t)lean_sarray_size(msg),
                                      lean_sarray_cptr(msg),
                                      lean_sarray_cptr(out))) {
        lean_dec_ref(out);
        return shim_none();
    }
    return shim_some(out);
}
