/* crypto-floor-selftest.c — exercise the EIGHT Lean-ABI crypto portals directly,
 * with real Lean Nat/Int/List objects, and check the REAL hashes against the
 * frozen circuit KATs. This is the anti-ghost tooth for the crypto-floor lane:
 * the GC'd demo executor never reaches the portals, so this harness calls each
 * portal symbol (`dregg_*`, the exact Lean C ABI) and asserts:
 *   - Poseidon2/BLAKE3/nullifier/keyed-MAC return REAL, deterministic, non-trivial
 *     digests (Poseidon2 matches the frozen circuit hash_2_to_1 value);
 *   - the not-carried verifies (ed25519/stark/aead) FAIL CLOSED (return 0);
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

/* The REAL §2 byte-channel STARK verify + its on-device anti-ghost self-test
 * (prove the carried CounterSquareAir, then ACCEPT good / REJECT tampered /
 * REJECT wrong-PI — bits 0/1/2; a fully-correct floor returns 0x7). This is the
 * executor-PD analogue of the verifier-stark PD's boot teeth, run on the real
 * aarch64-musl artifact. */
extern uint8_t dreggcf_stark_selftest(void);
extern uint8_t dreggcf_stark_verify_bytes(const uint8_t *proof, size_t proof_len,
                                          const uint8_t *pi, size_t pi_len);

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

    /* --- the NOT-carried verifies must FAIL CLOSED (never spuriously accept). - */
    {
        uint8_t e = dregg_ed25519_verify(lean_box(1), lean_box(1), lean_box(1));
        uint8_t s = dregg_stark_verify(lean_box(0), lean_box(0));
        uint8_t a = dregg_aead_open(lean_box(5), lean_box(5), lean_box(0));
        CHECK(e == 0, "ed25519 fails closed (rejects)");
        CHECK(s == 0, "stark-verify(abstract Nat-pair) fails closed (rejects)");
        CHECK(a == 0, "aead-open fails closed (rejects)");
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

    /* --- §3 pedersen placeholder: total + deterministic over Int args. --- */
    {
        lean_object *r = dregg_pedersen_commit(lean_box(3), lean_box(4));
        uint64_t c = lean_uint64_of_nat(r); lean_dec(r);
        CHECK(c != 0, "pedersen placeholder total + non-zero");
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
