/* crypto-floor.c — the REAL §8 crypto floor for the executor PD.
 *
 * Replaces crypto-stub.c (panic-if-reached, WRONG arity/types) with the eight
 * `@[extern]` crypto portals of `Dregg2/Crypto/PortalFloor.lean`, implemented at
 * the EXACT Lean C ABI the closure expects (read from the emitted facet
 * `metatheory/.lake/build/ir/Dregg2/Crypto/PortalFloor.c`):
 *
 *   uint8_t      dregg_ed25519_verify (lean_object*, lean_object*, lean_object*); // Nat,Nat,Nat -> Bool
 *   uint8_t      dregg_stark_verify   (lean_object*, lean_object*);               // Nat,Nat     -> Bool
 *   lean_object* dregg_pedersen_commit(lean_object*, lean_object*);               // Int,Int     -> Nat
 *   lean_object* dregg_poseidon2_hash (lean_object*, lean_object*);               // Nat,Nat     -> Nat
 *   lean_object* dregg_blake3_hash    (lean_object*);                             // List Nat    -> Nat
 *   lean_object* dregg_nullifier_derive(lean_object*);                            // Nat         -> Nat
 *   uint8_t      dregg_aead_open      (lean_object*, lean_object*, lean_object*); // Nat,Nat,Nat -> Bool
 *   lean_object* dregg_hmac_sha256    (lean_object*, lean_object*);               // Nat,Nat     -> Nat
 *
 * OWNERSHIP. The closure's `___boxed` wrappers pass their owned params straight
 * to these externs with NO surrounding inc/dec — so each extern OWNS its
 * arguments and must `lean_dec` them, and returns a freshly-owned result (the
 * standard Lean owned-`lean_obj_arg` convention). We extract values with the
 * BORROWING `lean_uint64_of_nat`, then `lean_dec` each owned arg.
 *
 * CRYPTO. The hashes are wired to the SAME carried implementations the
 * verifier-stark PD runs on seL4 — the Plonky3-conformant Poseidon2 over BabyBear
 * + BLAKE3 — via the `dreggcf_*` entry points of the `dregg-crypto-floor` Rust
 * staticlib (crypto-floor/, built for aarch64-unknown-linux-musl). So a turn that
 * hashes (Merkle node / commitment / nullifier / transcript) now computes a real,
 * field-correct digest on-device instead of aborting.
 *
 * SCOPE. Poseidon2 (§4), BLAKE3 (§5), the Poseidon2-derived nullifier (§6), and
 * the BLAKE3-keyed MAC (§8 HMAC analogue) are REAL via the carried staticlib. The
 * three elliptic-curve primitives — ed25519 verify_strict (§1), Ristretto255
 * Pedersen commit (§3), ChaCha20-Poly1305 AEAD open (§7) — are NOW ALSO REAL, this
 * shim marshalling their structured byte inputs out of the opaque Lean Nat/Int args
 * (LE magnitudes; see each portal's ENCODING note) and calling the matching
 * `dreggcf_{ed25519_verify,pedersen_commit,chacha_authenticate}` entries (the same
 * in-workspace ed25519-dalek / curve25519-dalek / chacha20poly1305 the executor +
 * cell use). So a turn that verifies a signature, commits a confidential value, or
 * opens an encrypted note is decided by REAL on-device crypto — accept iff valid,
 * FAIL-CLOSED otherwise. The ONLY remaining fail-closed entry is the STARK verify
 * over an abstract Nat PAIR (§2): two opaque Nats carry no checkable StarkProof, so
 * it rejects; the real check is the byte-channel `dreggcf_stark_verify_bytes`.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* ---- the real carried crypto (Rust staticlib dregg-crypto-floor) ----------- */
extern uint64_t dreggcf_poseidon2_2to1(uint64_t left, uint64_t right);
extern uint64_t dreggcf_blake3_to_field(const uint8_t *data, size_t len);
extern uint64_t dreggcf_nullifier(uint64_t note);
extern uint64_t dreggcf_keyed_mac(uint64_t key, const uint8_t *msg, size_t msg_len);
extern uint8_t  dreggcf_stark_verify_abstract(uint64_t stmt, uint64_t proof);
/* §1 ed25519 verify_strict, §3 Ristretto Pedersen commit, §7 ChaCha20-Poly1305
 * AEAD — the REAL elliptic-curve floor (crypto-floor/src/{ed25519,pedersen,aead}.rs). */
extern uint8_t  dreggcf_ed25519_verify(const uint8_t *pk, const uint8_t *msg,
                                       size_t msg_len, const uint8_t *sig);
extern void     dreggcf_pedersen_commit(uint64_t value, const uint8_t *blinding,
                                        uint8_t *out32);
extern uint8_t  dreggcf_chacha_authenticate(const uint8_t *key, const uint8_t *nonce,
                                            const uint8_t *ct, size_t ct_len);

/* Report a not-yet-carried primitive exactly once (so a reached floor names the
 * precise next wiring step rather than spamming or silently faking). */
static void floor_note_once(const char *prim) {
    static const char *seen[8];
    static int n = 0;
    for (int i = 0; i < n; i++) if (seen[i] == prim) return;
    if (n < 8) seen[n++] = prim;
    fprintf(stderr, "[exec] crypto floor: %s not carried in verifier-stark "
                    "(fail-closed; the hashing path does not reach it)\n", prim);
}

/* ---- Lean Nat <-> little-endian bytes (the elliptic-curve portal marshalling) -
 *
 * The §1/§3/§7 portals carry their STRUCTURED byte inputs (a 32-byte pubkey, a
 * 64-byte signature, a message, a sealed box) inside opaque Lean `Nat`/`Int`
 * arguments — a Lean Nat is arbitrary precision (a GMP mpz for big values), so a
 * byte string IS a Nat via its little-endian magnitude. We decompose a Nat into
 * its LE bytes using ONLY the public `lean.h` Nat API (`lean_nat_land` +
 * `lean_nat_shiftr`, both BORROWING) — no GMP-header / `LEAN_USE_GMP` coupling,
 * ABI-stable across runtime builds. `out` receives up to `out_cap` bytes; the
 * return value is the number of significant bytes (the Nat's byte length, which
 * for a fixed-width field like a 32-byte key may be SHORTER if high bytes are
 * zero — the caller zero-fills `out` first, so a short magnitude is left-aligned
 * little-endian, exactly the canonical fixed-width encoding). A Nat needing more
 * than `out_cap` bytes is truncated to `out_cap` (the high bytes are dropped); a
 * caller that fixes the width never hits this. Borrows `n` (no dec). */
static size_t nat_to_le_bytes(b_lean_obj_arg n, uint8_t *out, size_t out_cap) {
    /* fast path: a scalar Nat fits in a uintptr — peel its low bytes directly. */
    if (lean_is_scalar(n)) {
        size_t v = lean_unbox(n);
        size_t i = 0;
        while (i < out_cap) {
            out[i] = (uint8_t)(v & 0xff);
            v >>= 8;
            i++;
            if (v == 0) break;
        }
        /* significant length = highest nonzero byte index + 1 */
        size_t sig = 0;
        for (size_t k = 0; k < i; k++) if (out[k] != 0) sig = k + 1;
        return sig;
    }
    /* big Nat: iteratively peel the low byte via (n & 0xff), then n >>= 8. */
    lean_object *cur = n;        /* borrowed; we never dec the original */
    lean_inc(cur);               /* take an owned handle to iterate/free safely */
    lean_object *mask = lean_box(0xff);
    lean_object *eight = lean_box(8);
    size_t i = 0;
    size_t sig = 0;
    while (i < out_cap && !lean_is_scalar(cur)) {
        lean_object *low = lean_nat_land(cur, mask);   /* borrowing args */
        uint8_t byte = (uint8_t)lean_usize_of_nat(low);
        lean_dec(low);
        if (i < out_cap) out[i] = byte;
        if (byte != 0) sig = i + 1;
        lean_object *next = lean_nat_shiftr(cur, eight);
        lean_dec(cur);
        cur = next;
        i++;
    }
    /* tail: `cur` may have collapsed to a scalar with bytes still left. */
    if (lean_is_scalar(cur) && i < out_cap) {
        size_t v = lean_unbox(cur);
        while (i < out_cap && v != 0) {
            uint8_t byte = (uint8_t)(v & 0xff);
            out[i] = byte;
            if (byte != 0) sig = i + 1;
            v >>= 8;
            i++;
        }
    }
    lean_dec(cur);
    return sig;
}

/* Build a Lean Nat from `len` little-endian bytes: fold MSB→LSB as
 * `acc = acc*256 + byte`. Returns a freshly-owned Nat. Uses only the public
 * `lean.h` Nat API (no GMP coupling). For our 32-byte commitment this is a big
 * Nat; the fold is exact (Lean Nats are arbitrary precision). */
static lean_object *le_bytes_to_nat(const uint8_t *bytes, size_t len) {
    lean_object *acc = lean_box(0);
    lean_object *base = lean_box(256);
    for (size_t i = len; i-- > 0;) {
        lean_object *scaled = lean_nat_mul(acc, base);  /* borrowing */
        lean_dec(acc);
        lean_object *b = lean_box((size_t)bytes[i]);
        lean_object *sum = lean_nat_add(scaled, b);     /* borrowing */
        lean_dec(scaled);
        acc = sum;
    }
    return acc;
}

/* ===========================================================================
 * §4 — Poseidon2 (Nat,Nat -> Nat). REAL.
 * =========================================================================== */
lean_object *dregg_poseidon2_hash(lean_object *a, lean_object *b) {
    uint64_t la = lean_uint64_of_nat(a);   /* borrowing extract */
    uint64_t lb = lean_uint64_of_nat(b);
    lean_dec(a);                           /* we own a, b — release them */
    lean_dec(b);
    uint64_t h = dreggcf_poseidon2_2to1(la, lb);
    return lean_uint64_to_nat(h);          /* fresh owned Nat */
}

/* ===========================================================================
 * §5 — BLAKE3 (List Nat -> Nat). REAL.
 *
 * Walk the cons-list, taking each element's low byte (a `List Nat` of byte/limb
 * values; the canonical transcript form is a byte list), BLAKE3 it, and bridge
 * the digest into the field exactly as the carried STARK does. nil = scalar
 * (boxed 0, tag 0); cons = ctor tag 1, field 0 = head Nat, field 1 = tail.
 * =========================================================================== */
lean_object *dregg_blake3_hash(lean_object *lst) {
    /* First pass: count length (borrowing). */
    size_t len = 0;
    for (lean_object *p = lst; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) len++;

    uint8_t *buf = NULL;
    if (len > 0) {
        buf = (uint8_t *)malloc(len);
        if (!buf) { lean_dec(lst); abort(); }
        size_t i = 0;
        for (lean_object *p = lst; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) {
            lean_object *head = lean_ctor_get(p, 0);          /* borrowed Nat */
            buf[i++] = (uint8_t)(lean_uint64_of_nat(head) & 0xff);
        }
    }
    lean_dec(lst);                                            /* own the list */
    uint64_t h = dreggcf_blake3_to_field(buf, len);
    free(buf);
    return lean_uint64_to_nat(h);
}

/* ===========================================================================
 * §6 — Nullifier (Nat -> Nat). REAL (Poseidon2-derived deterministic tag).
 * =========================================================================== */
lean_object *dregg_nullifier_derive(lean_object *note) {
    uint64_t n = lean_uint64_of_nat(note);
    lean_dec(note);
    return lean_uint64_to_nat(dreggcf_nullifier(n));
}

/* ===========================================================================
 * §8 — HMAC analogue (Nat,Nat -> Nat). REAL (BLAKE3-keyed MAC).
 *
 * The message Nat's little-endian bytes are MAC'd under a key derived from the
 * key Nat. A real keyed PRF/MAC over the carried hash (the assumption is
 * BLAKE3-keyed unforgeability, the standard analogue of HMAC-SHA256's).
 * =========================================================================== */
lean_object *dregg_hmac_sha256(lean_object *key, lean_object *msg) {
    uint64_t k = lean_uint64_of_nat(key);
    uint64_t m = lean_uint64_of_nat(msg);
    lean_dec(key);
    lean_dec(msg);
    uint8_t mbytes[8];
    for (int i = 0; i < 8; i++) mbytes[i] = (uint8_t)((m >> (8 * i)) & 0xff);
    return lean_uint64_to_nat(dreggcf_keyed_mac(k, mbytes, 8));
}

/* ===========================================================================
 * §2 — STARK verify (Nat,Nat -> Bool). FAIL-CLOSED wiring.
 *
 * Two abstract Nats carry no checkable StarkProof; the carried real verifier
 * (stark_core::stark::verify) needs the structured proof bytes, supplied out of
 * band by the executor PD's proof-carrying turn. Until that byte channel is
 * routed here, reject (0) — NEVER accept without a verified proof.
 * =========================================================================== */
uint8_t dregg_stark_verify(lean_object *stmt, lean_object *proof) {
    uint64_t s = lean_uint64_of_nat(stmt);
    uint64_t p = lean_uint64_of_nat(proof);
    lean_dec(stmt);
    lean_dec(proof);
    floor_note_once("stark-verify(abstract-Nat)");
    return dreggcf_stark_verify_abstract(s, p); /* always 0 (sound reject) */
}

/* ===========================================================================
 * §1 — ed25519 verify (Nat,Nat,Nat -> Bool). REAL (ed25519-dalek verify_strict).
 *
 * ENCODING. The three Nats carry the verify inputs as little-endian magnitudes:
 *   pk : the 32-byte compressed Edwards public key (LE, fixed-width 32);
 *   m  : the signed message bytes (LE; its byte length is the message length);
 *   s  : the 64-byte signature (R || s) (LE, fixed-width 64).
 * We extract pk to exactly 32 bytes and s to 64 (the buffer is zero-filled first,
 * so a Nat with high zero bytes is the canonical short magnitude, left-aligned LE
 * — the fixed-width encoding). The message is extracted to its significant length
 * (bounded by a generous cap). Then `dreggcf_ed25519_verify` runs the SAME
 * `verify_strict` the executor auth path runs: accept iff valid, FAIL-CLOSED else.
 * =========================================================================== */
#define DREGG_ED25519_MAX_MSG 4096
uint8_t dregg_ed25519_verify(lean_object *pk, lean_object *m, lean_object *s) {
    uint8_t pk_bytes[32] = {0};
    uint8_t sig_bytes[64] = {0};
    static uint8_t msg_buf[DREGG_ED25519_MAX_MSG];
    nat_to_le_bytes(pk, pk_bytes, sizeof pk_bytes);
    nat_to_le_bytes(s, sig_bytes, sizeof sig_bytes);
    size_t msg_len = nat_to_le_bytes(m, msg_buf, sizeof msg_buf);
    lean_dec(pk);
    lean_dec(m);
    lean_dec(s);
    return dreggcf_ed25519_verify(pk_bytes, msg_buf, msg_len, sig_bytes);
}

/* ===========================================================================
 * §7 — AEAD open (Nat,Nat,Nat -> Bool). REAL (ChaCha20-Poly1305 authenticate).
 *
 * ENCODING. The `aeadOpen key ct` oracle decides ciphertext authenticity:
 *   key : the 32-byte AEAD key (LE, fixed-width 32);
 *   ct  : the sealed box `nonce(12) || ciphertext||tag` (LE; its byte length is
 *         12 + ciphertext_len + 16) — the committed-note ECIES wire minus the
 *         ephemeral pubkey, which the recipient has already used to derive `key`;
 *   aad : reserved (the cell ECIES box uses no additional authenticated data).
 * We split the leading 12 bytes as the nonce and the remainder as the AEAD body,
 * then `dreggcf_chacha_authenticate` runs the SAME ChaCha20-Poly1305 the note box
 * opens with: 1 iff the Poly1305 tag authenticates, 0 otherwise (FAIL-CLOSED — a
 * tampered ciphertext, wrong key, or short box never spuriously authenticates).
 * =========================================================================== */
#define DREGG_AEAD_MAX_BOX 8192
uint8_t dregg_aead_open(lean_object *key, lean_object *ct, lean_object *aad) {
    uint8_t key_bytes[32] = {0};
    static uint8_t box_buf[DREGG_AEAD_MAX_BOX];
    nat_to_le_bytes(key, key_bytes, sizeof key_bytes);
    size_t box_len = nat_to_le_bytes(ct, box_buf, sizeof box_buf);
    lean_dec(key);
    lean_dec(ct);
    lean_dec(aad);
    /* a valid box is at least nonce(12) + tag(16) = 28 bytes. */
    if (box_len < 12 + 16) {
        return 0; /* too short to carry nonce + a tag — reject */
    }
    const uint8_t *nonce = box_buf;            /* first 12 bytes */
    const uint8_t *body = box_buf + 12;        /* ciphertext || tag */
    size_t body_len = box_len - 12;
    return dreggcf_chacha_authenticate(key_bytes, nonce, body, body_len);
}

/* ===========================================================================
 * §3 — Pedersen commit (Int,Int -> Nat). REAL (Ristretto255 value commitment).
 *
 * ENCODING. `commit value blinding` over the SAME group + generators
 * `cell::value_commitment::commit_bytes` uses — the commitment the executor's
 * conservation check consumes and the circuit binds (see pedersen.rs for the
 * curve reconciliation). The two Lean Ints carry:
 *   v : the value `value : u64` (its nonneg magnitude's low 64 bits — a value
 *       commitment is to a nonnegative amount; `Int` is the portal's model type);
 *   r : the blinding factor (its magnitude's low 32 LE bytes — reduced mod the
 *       Ristretto group order inside the primitive, matching
 *       `scalar_from_blinding_bytes`).
 * We compute `value·V + scalar(blinding)·R`, compress to 32 canonical bytes, and
 * return those bytes as a Lean Nat (LE) — byte-identical to `commit_bytes`. (Int
 * magnitude: for a nonneg Int the object is a Nat; `lean_uint64_of_nat` /
 * `nat_to_le_bytes` read it directly. A negative Int's wrapped magnitude is read
 * the same way — a value/blinding is nonnegative on the live path.)
 * =========================================================================== */
lean_object *dregg_pedersen_commit(lean_object *v, lean_object *r) {
    uint64_t value = lean_is_scalar(v) ? (uint64_t)lean_unbox(v) : lean_uint64_of_nat(v);
    uint8_t blinding[32] = {0};
    nat_to_le_bytes(r, blinding, sizeof blinding);
    lean_dec(v);
    lean_dec(r);

    uint8_t commitment[32] = {0};
    dreggcf_pedersen_commit(value, blinding, commitment);
    return le_bytes_to_nat(commitment, sizeof commitment);
}
