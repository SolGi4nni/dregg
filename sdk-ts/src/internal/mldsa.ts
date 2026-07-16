/**
 * The post-quantum half of a HYBRID turn authorization: ML-DSA-65 (FIPS 204).
 *
 * Mirrors `dregg-pq/src/mldsa.rs` (`MlDsaKey`) and `turn/src/pq.rs`
 * (`MlDsaTurnKey`, which pins the turn domain-separation context). Every
 * constant and convention here is a mirror of a Rust source of truth; drift
 * fails the differential in `test/wire.test.mjs` against a freshly-built
 * `dregg-wasm` oracle.
 *
 * ## Why `@noble/post-quantum`
 *
 * The SDK's front door is deliberately wasm-free (see `PUBLISHED-VERIFY.md`):
 * `dregg-wasm` is not published to npm and is only a dev-time differential
 * oracle / legacy-subpath peer. Routing the DEFAULT signer through wasm would
 * make every signed turn depend on an unpublished package — so the signer is
 * pure JS, from the same family (`@noble/ed25519`, `@noble/hashes`) the SDK
 * already depends on, by the same maintainer, audited and actively maintained.
 * It is a real FIPS 204 implementation, not a hand-roll: NO lattice arithmetic
 * is written here, only the parameter/derivation/context plumbing that pins it
 * to dregg's conventions. Its ML-DSA-65 lengths agree with the Rust crate's
 * (`pk` 1952, `sig` 3309, `sk` 4032), and the byte-identity of what it produces
 * is *driven* against the Rust oracle rather than assumed.
 */

import { ml_dsa65 } from "@noble/post-quantum/ml-dsa.js";

import { utf8 } from "./bytes";

/**
 * FIPS 204 `ctx` for the ML-DSA half of a HYBRID *turn* authorization, bound
 * into every signature — `turn/src/pq.rs::HYBRID_TURN_PQ_CTX`.
 *
 * Distinct from the consensus quorum context (`dregg-hybrid-qc-v1`) so a
 * turn-path PQ signature can never be replayed as a quorum-certificate half.
 * Signer and verifier MUST agree on it.
 */
export const HYBRID_TURN_PQ_CTX: Uint8Array = utf8.encode("dregg-hybrid-turn-v1");

/** Serialized ML-DSA-65 public key length (`dregg_pq::ML_DSA_PK_LEN`). */
export const ML_DSA_PK_LEN = 1952;

/** Serialized ML-DSA-65 signature length (`dregg_pq::ML_DSA_SIG_LEN`). */
export const ML_DSA_SIG_LEN = 3309;

/** Serialized ML-DSA-65 secret key length (`dregg_pq::ML_DSA_SK_LEN`). */
export const ML_DSA_SK_LEN = 4032;

/** An ML-DSA-65 keypair, derived from an ed25519 seed. */
export interface MlDsaKeypair {
  /** The serialized ML-DSA-65 public key (carried in the hybrid envelope). */
  readonly publicKey: Uint8Array;
  /** The serialized ML-DSA-65 secret key (key material — never logged). */
  readonly secretKey: Uint8Array;
}

/**
 * Derive the ML-DSA-65 keypair DETERMINISTICALLY from the SAME 32-byte ed25519
 * seed the classical identity uses — FIPS 204 `ML-DSA.KeyGen(ξ = seed)`.
 * Mirror of `dregg_pq::MlDsaKey::from_ed25519_seed`
 * (`ml_dsa_65::KG::keygen_from_seed(seed)`).
 *
 * This is why a hybrid identity needs NO new key material and no separate
 * ceremony: a cipherclerk, a node, and a genesis fixture built from one
 * mnemonic all agree on the PQ public key. A verifier cannot derive another
 * party's PQ *public* key from their ed25519 *public* key, which is why the
 * ML-DSA public key is carried in the hybrid envelope.
 */
export function mlDsaKeypairFromEd25519Seed(seed32: Uint8Array): MlDsaKeypair {
  const { publicKey, secretKey } = ml_dsa65.keygen(seed32);
  return { publicKey, secretKey };
}

/**
 * Sign `message` under {@link HYBRID_TURN_PQ_CTX} with the DETERMINISTIC FIPS
 * 204 variant (`rnd = {0}^32`) — mirror of
 * `dregg_pq::MlDsaKey::try_sign_deterministic`, which
 * `turn/src/pq.rs::MlDsaTurnKey::sign` calls.
 *
 * Determinism is REQUIRED, not incidental: the ML-DSA half is bound into
 * `Action::hash` (discriminant 10 — the anti-strip binding), which flows into
 * `Turn::hash`. A hedged/randomized signature would make the SAME logical turn
 * hash DIFFERENTLY on each signing, breaking turn identity (receipt matching,
 * dedup, exactly-once). `extraEntropy: false` selects the zero `rnd`, which is
 * exactly what the Rust path does (`try_sign_with_seed(&[0u8; 32], …)`, whose
 * zero seed drives the crate's `DummyRng`).
 */
export function mlDsaSign(secretKey: Uint8Array, message: Uint8Array): Uint8Array {
  return ml_dsa65.sign(message, secretKey, {
    context: HYBRID_TURN_PQ_CTX,
    extraEntropy: false,
  });
}

/**
 * Verify an ML-DSA-65 signature over `message` under {@link HYBRID_TURN_PQ_CTX}
 * — mirror of `turn/src/pq.rs::ml_dsa_verify`.
 *
 * Returns `false` — never throws — on a wrong-length key/signature or a failed
 * check. This is the fail-CLOSED primitive: a present-but-invalid PQ half must
 * make the whole hybrid authorization reject, regardless of `require_pq`.
 */
export function mlDsaVerify(
  publicKey: Uint8Array,
  message: Uint8Array,
  signature: Uint8Array,
): boolean {
  if (publicKey.length !== ML_DSA_PK_LEN || signature.length !== ML_DSA_SIG_LEN) {
    return false;
  }
  try {
    return ml_dsa65.verify(signature, message, publicKey, { context: HYBRID_TURN_PQ_CTX });
  } catch {
    return false;
  }
}
