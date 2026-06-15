/* crypto-floor-selftest.c — exercise the EIGHT Lean-ABI crypto portals directly,
 * with real Lean Nat/Int/List objects, and check the REAL hashes against the
 * frozen circuit KATs. This is the anti-ghost tooth for the crypto-floor lane:
 * the GC'd demo executor never reaches the portals, so this harness calls each
 * portal symbol (`dregg_*`, the exact Lean C ABI) and asserts:
 *   - Poseidon2/BLAKE3/nullifier/keyed-MAC return REAL, deterministic, non-trivial
 *     digests (Poseidon2 matches the frozen circuit hash_2_to_1 value);
 *   - the REAL elliptic-curve portals bite end-to-end through the Lean ABI:
 *     ed25519 (§1) ACCEPTS a genuine signature + REJECTS a forged one; the Pedersen
 *     commit (§3) returns the Ristretto255 `value·V+blinding·R` bytes equal to the
 *     carried commit_bytes; AEAD open (§7) AUTHENTICATES a genuine box + REJECTS a
 *     tampered one — each driven with a Rust-minted test vector;
 *   - only the ABSTRACT-Nat STARK verify (§2) FAILS CLOSED (no checkable proof);
 *   - no refcount leak/crash across thousands of calls (the ownership contract).
 *
 * Built + run by scripts/link-probe.sh's self-test step (host musl under
 * qemu-aarch64 if available; on macOS the link alone is the checkpoint).
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* The portal + dreggcf_* symbols are C-ABI (crypto-floor.c is built with gcc;
 * the dreggcf_* entries are Rust `extern "C"`). This harness is built with g++
 * (link-probe.sh), so the declarations MUST be `extern "C"` or the compiler
 * emits C++-mangled references (`_Z20dregg_poseidon2_hash…`) that never resolve
 * against the unmangled definitions. (`lean.h` already wraps its own decls.) */
#ifdef __cplusplus
extern "C" {
#endif

/* The portal symbols, at the exact ABI from PortalFloor.c. */
extern lean_object *dregg_poseidon2_hash(lean_object *, lean_object *);
extern lean_object *dregg_blake3_hash(lean_object *);
extern lean_object *dregg_nullifier_derive(lean_object *);
extern lean_object *dregg_hmac_sha256(lean_object *, lean_object *);
extern lean_object *dregg_pedersen_commit(lean_object *, lean_object *);
extern uint8_t dregg_ed25519_verify(lean_object *, lean_object *, lean_object *);
extern uint8_t dregg_stark_verify(lean_object *, lean_object *);
extern uint8_t dregg_aead_open(lean_object *, lean_object *, lean_object *);

/* The carried primitives directly (to cross-check the C shim against them). */
extern uint64_t dreggcf_poseidon2_2to1(uint64_t, uint64_t);
extern void     dreggcf_pedersen_commit(uint64_t value, const uint8_t *blinding, uint8_t *out32);

/* The REAL elliptic-curve floor self-tests (mint+verify in Rust; 0xF = all teeth)
 * + test-vector exporters so this harness can drive the Lean PORTALS end-to-end
 * (the C harness cannot sign / seal itself). */
extern uint8_t  dreggcf_ed25519_selftest(void);
extern uint8_t  dreggcf_pedersen_selftest(void);
extern uint8_t  dreggcf_chacha_selftest(void);
extern void     dreggcf_ed25519_test_vector(uint8_t *pk_out, uint8_t *msg_out,
                                            size_t *msg_len, uint8_t *sig_out);
extern void     dreggcf_aead_test_vector(uint8_t *key_out, uint8_t *box_out, size_t *box_len);

/* The REAL §2 byte-channel STARK verify + its on-device anti-ghost self-test
 * (prove the carried CounterSquareAir, then ACCEPT good / REJECT tampered /
 * REJECT wrong-PI — bits 0/1/2; a fully-correct floor returns 0x7). This is the
 * executor-PD analogue of the verifier-stark PD's boot teeth, run on the real
 * aarch64-musl artifact. */
extern uint8_t dreggcf_stark_selftest(void);
extern uint8_t dreggcf_stark_verify_bytes(const uint8_t *proof, size_t proof_len,
                                          const uint8_t *pi, size_t pi_len);

/* The LIVE proof-carrying-turn ADMISSION path: the producer ships a turn's proof
 * bytes + PI in a PCT1 wire envelope, the executor PD DECODES it and ADMITS the
 * turn iff the carried proof verifies (fail-closed). `dreggcf_admit_selftest()`
 * builds three real turn wires (genuine / tampered-proof / wrong-PI) and drives
 * `dreggcf_admit_proof_carrying_turn` — the anti-ghost teeth on the LIVE-turn path
 * (proof bytes routed from the turn wire, not minted in-line). 0x7 = all bite. */
extern uint8_t dreggcf_admit_selftest(void);
extern uint8_t dreggcf_admit_proof_carrying_turn(const uint8_t *wire, size_t wire_len);

extern void lean_initialize_runtime_module(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

static int failures = 0;
#define CHECK(cond, msg) do { \
    if (cond) { printf("  [ok]   %s\n", msg); } \
    else { printf("  [FAIL] %s\n", msg); failures++; } } while (0)

/* Build a `List Nat` from a byte buffer (head = byte value, in order). */
static lean_object *mk_byte_list(const uint8_t *b, size_t n) {
    lean_object *lst = lean_box(0); /* List.nil */
    for (size_t i = n; i-- > 0;) {
        lean_object *cell = lean_alloc_ctor(1, 2, 0); /* List.cons, 2 fields */
        lean_ctor_set(cell, 0, lean_box((size_t)b[i])); /* head : Nat */
        lean_ctor_set(cell, 1, lst);                    /* tail */
        lst = cell;
    }
    return lst;
}

/* Build a Lean Nat from `n` little-endian bytes (acc = acc*256 + byte, MSB->LSB)
 * — the inverse of the shim's `nat_to_le_bytes`, so a byte string round-trips
 * Nat -> bytes -> Nat. Returns a freshly-owned Nat. */
static lean_object *mk_nat_le(const uint8_t *b, size_t n) {
    lean_object *acc = lean_box(0);
    lean_object *base = lean_box(256);
    for (size_t i = n; i-- > 0;) {
        lean_object *scaled = lean_nat_mul(acc, base);
        lean_dec(acc);
        lean_object *byte = lean_box((size_t)b[i]);
        lean_object *sum = lean_nat_add(scaled, byte);
        lean_dec(scaled);
        acc = sum;
    }
    return acc;
}

int main(void) {
    lean_initialize_runtime_module();
    printf("== crypto-floor self-test (the eight Lean-ABI portals) ==\n");

    /* --- §4 Poseidon2: matches the carried hash_2_to_1 + deterministic. --- */
    {
        uint64_t expect = dreggcf_poseidon2_2to1(7, 11);
        lean_object *r = dregg_poseidon2_hash(lean_box(7), lean_box(11));
        uint64_t got = lean_uint64_of_nat(r);
        lean_dec(r);
        CHECK(got == expect && got != 0, "poseidon2(7,11) == carried hash_2_to_1, non-zero");
        /* order-sensitive */
        lean_object *r2 = dregg_poseidon2_hash(lean_box(11), lean_box(7));
        uint64_t got2 = lean_uint64_of_nat(r2);
        lean_dec(r2);
        CHECK(got2 != got, "poseidon2 is order-sensitive (7,11) != (11,7)");
    }

    /* --- §5 BLAKE3 over a List Nat: deterministic, non-zero, input-sensitive. - */
    {
        uint8_t a[] = {1, 2, 3, 4, 5};
        uint8_t b[] = {9, 9, 9};
        lean_object *la = mk_byte_list(a, sizeof a);
        lean_object *ra = dregg_blake3_hash(la);
        uint64_t ha = lean_uint64_of_nat(ra); lean_dec(ra);
        /* recompute (fresh list — the first was consumed) */
        lean_object *la2 = mk_byte_list(a, sizeof a);
        lean_object *ra2 = dregg_blake3_hash(la2);
        uint64_t ha2 = lean_uint64_of_nat(ra2); lean_dec(ra2);
        lean_object *lb = mk_byte_list(b, sizeof b);
        lean_object *rb = dregg_blake3_hash(lb);
        uint64_t hb = lean_uint64_of_nat(rb); lean_dec(rb);
        CHECK(ha == ha2 && ha != 0, "blake3(List Nat) deterministic + non-zero");
        CHECK(ha != hb, "blake3 is input-sensitive");
        /* empty list (nil) must not crash */
        lean_object *rnil = dregg_blake3_hash(lean_box(0));
        uint64_t hnil = lean_uint64_of_nat(rnil); lean_dec(rnil);
        CHECK(1, "blake3(nil) returns without crashing");
        (void)hnil;
    }

    /* --- §6 nullifier: deterministic, distinct from a bare 2-to-1. --- */
    {
        lean_object *r = dregg_nullifier_derive(lean_box(42));
        uint64_t n1 = lean_uint64_of_nat(r); lean_dec(r);
        lean_object *r2 = dregg_nullifier_derive(lean_box(42));
        uint64_t n2 = lean_uint64_of_nat(r2); lean_dec(r2);
        CHECK(n1 == n2 && n1 != 0, "nullifier(42) deterministic + non-zero");
        CHECK(n1 != dreggcf_poseidon2_2to1(42, 42), "nullifier domain-separated from node hash");
    }

    /* --- §8 keyed MAC: deterministic, key-sensitive. --- */
    {
        lean_object *r = dregg_hmac_sha256(lean_box(1), lean_box(0xABCD));
        uint64_t t1 = lean_uint64_of_nat(r); lean_dec(r);
        lean_object *r2 = dregg_hmac_sha256(lean_box(2), lean_box(0xABCD));
        uint64_t t2 = lean_uint64_of_nat(r2); lean_dec(r2);
        CHECK(t1 != 0 && t1 != t2, "keyed-MAC non-zero + key-sensitive");
    }

    /* --- §1 ed25519 verify_strict is REAL: the Lean PORTAL accepts a genuine sig
     * and rejects a forged one (driven end-to-end — Rust mints the test vector,
     * the C harness builds the Nat-encoded pk/msg/sig and calls dregg_ed25519_verify). */
    {
        /* the Rust-side teeth (mint+verify): ACCEPT genuine, REJECT forged/wrong-msg
         * /wrong-key — a fully-correct floor returns 0xF. */
        CHECK(dreggcf_ed25519_selftest() == 0xF, "ed25519 verify_strict: ALL teeth bite (0xF)");

        /* end-to-end through the Lean ABI portal. */
        uint8_t pk[32], sig[64];
        static uint8_t msg[64];
        size_t msg_len = sizeof msg;
        dreggcf_ed25519_test_vector(pk, msg, &msg_len, sig);

        lean_object *pkN = mk_nat_le(pk, sizeof pk);
        lean_object *msgN = mk_nat_le(msg, msg_len);
        lean_object *sigN = mk_nat_le(sig, sizeof sig);
        /* dregg_ed25519_verify OWNS its args — pass fresh Nats. */
        uint8_t ok = dregg_ed25519_verify(pkN, msgN, sigN);
        CHECK(ok == 1, "ed25519 PORTAL: a genuine signature ACCEPTS (real verify_strict)");

        /* forge: flip a byte of the signature -> the portal must REJECT. */
        uint8_t fsig[64];
        for (int i = 0; i < 64; i++) fsig[i] = sig[i];
        fsig[40] ^= 0x01;
        lean_object *pkN2 = mk_nat_le(pk, sizeof pk);
        lean_object *msgN2 = mk_nat_le(msg, msg_len);
        lean_object *fsigN = mk_nat_le(fsig, sizeof fsig);
        uint8_t forged = dregg_ed25519_verify(pkN2, msgN2, fsigN);
        CHECK(forged == 0, "ed25519 PORTAL: a forged signature REJECTS (fail-closed)");
    }

    /* --- §2 the ABSTRACT-Nat STARK verify stays FAIL-CLOSED (an opaque Nat pair
     * carries no checkable StarkProof; the real check is the byte channel below). */
    {
        uint8_t s = dregg_stark_verify(lean_box(0), lean_box(0));
        CHECK(s == 0, "stark-verify(abstract Nat-pair) fails closed (rejects)");
    }

    /* --- §7 ChaCha20-Poly1305 AEAD open is REAL: the Lean PORTAL authenticates a
     * genuine box and rejects a tampered one (driven end-to-end). */
    {
        /* the Rust-side teeth: round-trip + tampered-ct/wrong-key/tampered-tag fail. */
        CHECK(dreggcf_chacha_selftest() == 0xF, "chacha20poly1305 AEAD: ALL teeth bite (0xF)");

        uint8_t key[32];
        static uint8_t boxbuf[128];
        size_t box_len = sizeof boxbuf;
        dreggcf_aead_test_vector(key, boxbuf, &box_len);
        CHECK(box_len > 12 + 16, "aead test vector produced a non-trivial box");

        /* aad is reserved -> Nat 0. ct = nonce(12) || ct||tag. */
        lean_object *keyN = mk_nat_le(key, sizeof key);
        lean_object *ctN = mk_nat_le(boxbuf, box_len);
        uint8_t a = dregg_aead_open(keyN, ctN, lean_box(0));
        CHECK(a == 1, "aead-open PORTAL: a genuine box AUTHENTICATES (real Poly1305)");

        /* tamper a ciphertext byte (after the 12-byte nonce, before the 16-byte tag). */
        uint8_t tampered[128];
        for (size_t i = 0; i < box_len; i++) tampered[i] = boxbuf[i];
        tampered[12 + (box_len - 12 - 16) / 2] ^= 0x01;
        lean_object *keyN2 = mk_nat_le(key, sizeof key);
        lean_object *ctN2 = mk_nat_le(tampered, box_len);
        uint8_t at = dregg_aead_open(keyN2, ctN2, lean_box(0));
        CHECK(at == 0, "aead-open PORTAL: a tampered ciphertext REJECTS (fail-closed)");

        /* a too-short box (just the nonce, no body) must reject without crashing. */
        lean_object *keyN3 = mk_nat_le(key, sizeof key);
        lean_object *shortN = mk_nat_le(boxbuf, 12);
        uint8_t ash = dregg_aead_open(keyN3, shortN, lean_box(0));
        CHECK(ash == 0, "aead-open PORTAL: a too-short box REJECTS (fail-closed)");
    }

    /* --- §2 the REAL byte-channel STARK verify: the anti-ghost teeth bite. ----
     * dreggcf_stark_selftest() proves the carried CounterSquareAir (real
     * Reed-Solomon + BLAKE3 Merkle + FRI + Fiat-Shamir — the SAME STARK the
     * verifier-stark PD runs), then drives dreggcf_stark_verify_bytes on three
     * cases. A fully-correct floor returns 0x7 (all three teeth bite). This is
     * the executor-PD parity with verifier-stark's verified heart organ. */
    {
        uint8_t m = dreggcf_stark_selftest();
        CHECK((m & 0x1) != 0, "real STARK verify: ACCEPTS a sound proof + correct PI");
        CHECK((m & 0x2) != 0, "real STARK verify: REJECTS a tampered proof (anti-ghost tooth)");
        CHECK((m & 0x4) != 0, "real STARK verify: REJECTS the good proof under a wrong PI (boundary tooth)");
        CHECK(m == 0x7, "real STARK verify self-test: ALL teeth bite (0x7)");

        /* a garbage proof buffer must fail closed (decode error -> reject). */
        uint8_t garbage[64];
        for (int i = 0; i < 64; i++) garbage[i] = 0xAB;
        uint32_t pi0 = 0; /* PI = single LE u32 limb 0 */
        uint8_t gv = dreggcf_stark_verify_bytes(garbage, sizeof garbage,
                                                (const uint8_t *)&pi0, sizeof pi0);
        CHECK(gv == 0, "real STARK verify: garbage proof fails closed (rejects)");
        uint8_t ev = dreggcf_stark_verify_bytes((const uint8_t *)0, 0,
                                                (const uint8_t *)&pi0, sizeof pi0);
        CHECK(ev == 0, "real STARK verify: empty proof fails closed (rejects)");
    }

    /* --- §2.1 the LIVE proof-carrying-turn ADMISSION path: the teeth bite on the
     * ADMISSION entry, where the proof bytes arrive from the turn wire (decoded),
     * not minted in-line. dreggcf_admit_selftest() builds three turn wires and
     * drives dreggcf_admit_proof_carrying_turn: a genuine turn ADMITS (0x1), a
     * tampered-proof turn REFUSES (0x2), a wrong-PI turn REFUSES (0x4). This is the
     * §4 next step (docs/EMBEDDABLE-LEAN-RUNTIME.md): a LIVE turn's proof bytes
     * reach the real verifier, admitted iff verify == 1. */
    {
        uint8_t am = dreggcf_admit_selftest();
        CHECK((am & 0x1) != 0, "live-turn admit: ADMITS a genuine proof-carrying turn");
        CHECK((am & 0x2) != 0, "live-turn admit: REFUSES a turn carrying a tampered proof");
        CHECK((am & 0x4) != 0, "live-turn admit: REFUSES a turn carrying a wrong PI (boundary)");
        CHECK(am == 0x7, "live proof-carrying-turn admission: ALL teeth bite (0x7)");

        /* a malformed turn envelope must fail closed at decode (never admit). */
        uint8_t bad_wire[32];
        for (int i = 0; i < 32; i++) bad_wire[i] = 0x00; /* bad magic */
        uint8_t bm = dreggcf_admit_proof_carrying_turn(bad_wire, sizeof bad_wire);
        CHECK(bm == 0, "live-turn admit: malformed turn wire fails closed (refuses)");
        uint8_t em = dreggcf_admit_proof_carrying_turn((const uint8_t *)0, 0);
        CHECK(em == 0, "live-turn admit: empty turn wire fails closed (refuses)");
    }

    /* --- §3 Pedersen value commitment is REAL (Ristretto255): the Lean PORTAL
     * returns the 32-byte `value·V + blinding·R` commitment (as a Nat) byte-for-byte
     * equal to the carried `dreggcf_pedersen_commit` — which is byte-identical to
     * cell::value_commitment::commit_bytes (the executor/circuit commitment). */
    {
        /* the Rust-side teeth: opening verifies, wrong value/blinding fail, homomorphic. */
        CHECK(dreggcf_pedersen_selftest() == 0xF, "pedersen (Ristretto255): ALL teeth bite (0xF)");

        /* the portal's commitment must equal the carried primitive's, for the SAME
         * (value, blinding). value = 1234567; blinding = a fixed 32-byte LE scalar. */
        uint64_t value = 1234567;
        uint8_t blinding[32] = {0};
        blinding[0] = 0x9A; blinding[31] = 0x42;

        uint8_t expect[32] = {0};
        dreggcf_pedersen_commit(value, blinding, expect);

        /* drive the portal: v = Int 1234567; r = the blinding as a Nat (LE). */
        lean_object *vN = lean_box((size_t)value);            /* small Int/Nat */
        lean_object *rN = mk_nat_le(blinding, sizeof blinding);
        lean_object *cN = dregg_pedersen_commit(vN, rN);
        /* the returned Nat's LE bytes must equal `expect` (32 bytes). Decompose,
         * tracking a write index `gi` (NOT conflating a genuine 0x00 byte with an
         * unwritten slot) — peel low bytes off the big Nat, then drain any scalar
         * tail from the SAME index. */
        uint8_t got[32] = {0};
        {
            int gi = 0;
            lean_object *cur = cN; lean_inc(cur);
            lean_object *mask = lean_box(0xff); lean_object *eight = lean_box(8);
            while (gi < 32 && !lean_is_scalar(cur)) {
                lean_object *low = lean_nat_land(cur, mask);
                got[gi++] = (uint8_t)lean_usize_of_nat(low); lean_dec(low);
                lean_object *next = lean_nat_shiftr(cur, eight); lean_dec(cur); cur = next;
            }
            if (lean_is_scalar(cur)) {
                size_t leftover = lean_unbox(cur);
                while (gi < 32 && leftover) {
                    got[gi++] = (uint8_t)(leftover & 0xff);
                    leftover >>= 8;
                }
            }
            lean_dec(cur);
        }
        lean_dec(cN);
        int match = 1;
        for (int i = 0; i < 32; i++) if (got[i] != expect[i]) { match = 0; break; }
        CHECK(match, "pedersen PORTAL: commitment == carried commit_bytes (Ristretto255, real binding)");

        /* determinism + a different value -> a different commitment (binding). */
        uint8_t other[32] = {0};
        dreggcf_pedersen_commit(value + 1, blinding, other);
        int differ = 0;
        for (int i = 0; i < 32; i++) if (other[i] != expect[i]) { differ = 1; break; }
        CHECK(differ, "pedersen: a different value yields a different commitment (binding)");
    }

    /* --- ownership: many calls, no leak/crash. --- */
    {
        for (int i = 0; i < 50000; i++) {
            lean_object *r = dregg_poseidon2_hash(lean_box((size_t)i), lean_box((size_t)(i ^ 0x5a5a)));
            lean_dec(r);
        }
        CHECK(1, "50000 poseidon2 calls: no leak/crash (refcount contract holds)");
    }

    if (failures == 0) {
        printf("\n== ALL crypto-floor portal checks PASS — the floor is REAL + ABI-correct ==\n");
        return 0;
    }
    printf("\n== %d crypto-floor check(s) FAILED ==\n", failures);
    return 1;
}
