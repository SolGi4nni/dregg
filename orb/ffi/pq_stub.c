/* ffi/pq_stub.c — fail-closed post-quantum seam stubs for the standalone,
 * pure-Lean serve executables (orb / orb-mac-multi / orb-quic and the other
 * `lean_exe`s that link the crypto shim).
 *
 * Those exes link ffi/crypto_shim.o, whose ML-DSA-65 / ML-KEM-768 crossings
 * (drorb_ml_dsa_verify / drorb_ml_kem_{encaps,decaps}) reference the dregg-pq
 * wire (drorb_pq_*). But a pure-Lean exe cannot link dregg-pq — a Rust crate
 * that is a path-dependency of the dataplane crate ONLY. Without a definition
 * of drorb_pq_* the exe link fails undefined. These stubs provide the symbols so
 * those exes LINK; each fails CLOSED (verify rejects; encaps/decaps report
 * failure), the honest floor for a binary that lacks the post-quantum core.
 *
 * The DEPLOYED dataplane binary does NOT link this object: it links the REAL
 * dregg-backed drorb_pq_* (crates/dataplane/src/pq.rs -> dregg_pq), which is that
 * binary's SOLE strong definition of these symbols. Conformance never drives the
 * PQ hybrid path (JWT Alg.hybrid / TLS X25519MLKEM768), so the standalone exes
 * never reach these stubs at runtime — they exist purely to keep the link total. */
#include <stdint.h>
#include <stddef.h>

uint8_t drorb_pq_ml_dsa_verify(
        const uint8_t *pk, size_t pk_len,
        const uint8_t *msg, size_t msg_len,
        const uint8_t *sig, size_t sig_len,
        const uint8_t *ctx, size_t ctx_len) {
    (void) pk; (void) pk_len; (void) msg; (void) msg_len;
    (void) sig; (void) sig_len; (void) ctx; (void) ctx_len;
    return 0u; /* fail-closed: reject */
}

uint8_t drorb_pq_ml_kem_encaps(
        const uint8_t *ek, size_t ek_len, uint8_t *out) {
    (void) ek; (void) ek_len; (void) out;
    return 0u; /* fail-closed: encapsulation unavailable */
}

uint8_t drorb_pq_ml_kem_decaps(
        const uint8_t *dk, size_t dk_len,
        const uint8_t *ct, size_t ct_len, uint8_t *out) {
    (void) dk; (void) dk_len; (void) ct; (void) ct_len; (void) out;
    return 0u; /* fail-closed: decapsulation unavailable */
}
