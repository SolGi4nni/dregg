/**
 * `Identity` — the cipherclerk: who is acting.
 *
 * The first half of the SDK's authorization-first shape:
 *
 * ```text
 * Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
 * ```
 *
 * Key derivation is the SAME as the Rust SDK / CLI / extension:
 * `blake3::derive_key("dregg/0", seed64)` → 32-byte Ed25519 seed → keypair
 * (sdk/src/mnemonic.rs `derive_keypair`). All implementations pin the same
 * golden vector (seed `00..3f` → pubkey `335840a9…8b9a`), so any drift fails
 * everywhere at once.
 */

import { blake3DeriveKey } from "./internal/blake3";
import { ed25519PublicKey, ed25519Sign } from "./internal/ed25519";
import { exactBytes, hexEncode } from "./internal/bytes";
import type { MlDsaKeypair } from "./internal/mldsa";
import { mlDsaKeypairFromEd25519Seed, mlDsaSign } from "./internal/mldsa";
import type { Action, CellId, Turn } from "./internal/wire";
import { actionSigningMessage, deriveCellId, encodeSignedTurn, turnHash } from "./internal/wire";

/** The main-agent derivation path. Sub-agents use `dregg/1`, `dregg/2`, … */
export const MAIN_IDENTITY_PATH = "dregg/0";

/**
 * A local signing identity (Ed25519). Construct from a 64-byte master seed
 * (profile store shape), a raw 32-byte Ed25519 seed, or a named profile
 * (see `profiles.ts`).
 */
export class Identity {
  /** The 32-byte Ed25519 seed (key material — never logged). */
  private readonly seed: Uint8Array;
  /** The 32-byte Ed25519 public key. */
  readonly publicKey: Uint8Array;

  private constructor(seed32: Uint8Array) {
    this.seed = exactBytes(seed32, 32, "ed25519 seed");
    this.publicKey = ed25519PublicKey(this.seed);
  }

  /**
   * Derive the main identity from a 64-byte master seed at path `dregg/0`
   * (the profile-store derivation — mirrors `AgentCipherclerk::from_seed`).
   */
  static fromSeed(seed64: Uint8Array, path: string = MAIN_IDENTITY_PATH): Identity {
    exactBytes(seed64, 64, "master seed");
    return new Identity(blake3DeriveKey(path, seed64));
  }

  /** Wrap a raw 32-byte Ed25519 seed directly (no path derivation). */
  static fromKeyBytes(seed32: Uint8Array): Identity {
    return new Identity(seed32);
  }

  /** A fresh random identity (OS randomness). */
  static generate(): Identity {
    const seed = new Uint8Array(64);
    globalThis.crypto.getRandomValues(seed);
    return Identity.fromSeed(seed);
  }

  /** Hex Ed25519 public key (the profile store's `public_key_hex`). */
  get publicKeyHex(): string {
    return hexEncode(this.publicKey);
  }

  /**
   * This identity's default agent cell:
   * `CellId::derive_raw(publicKey, blake3("default"))` — the cell the node
   * requires as `turn.agent` for envelope-signed submissions.
   */
  cellId(): CellId {
    return deriveCellId(this.publicKey);
  }

  /** Hex form of [`cellId`]. */
  cellIdHex(): string {
    return hexEncode(this.cellId());
  }

  /** Sign arbitrary bytes (Ed25519, deterministic). */
  signBytes(message: Uint8Array): Uint8Array {
    return ed25519Sign(this.seed, message);
  }

  /**
   * The identity's ML-DSA-65 keypair, derived deterministically from the SAME
   * ed25519 seed (`MlDsaTurnKey::from_ed25519_seed`). Cached: keygen is the
   * expensive part of hybrid signing, and the key is a pure function of the
   * seed.
   */
  private mlDsaCache?: MlDsaKeypair;

  private mlDsaKey(): MlDsaKeypair {
    return (this.mlDsaCache ??= mlDsaKeypairFromEd25519Seed(this.seed));
  }

  /**
   * This identity's serialized ML-DSA-65 public key (1952 bytes) — the PQ half
   * of the hybrid identity, derived from the same seed as the ed25519 key.
   * A verifier cannot derive it from the ed25519 *public* key, which is why
   * every hybrid authorization carries it.
   */
  mlDsaPublicKey(): Uint8Array {
    return this.mlDsaKey().publicKey;
  }

  /**
   * Sign an action with a HYBRID (ed25519 + ML-DSA-65) authorization — the
   * DEFAULT, byte-identical to Rust's `AgentCipherclerk::sign_action`.
   *
   * Both halves cover the SAME canonical signing message
   * (`dregg-action-sig-v3`); the ML-DSA half is deterministic (FIPS 204
   * `rnd = {0}^32`) so the turn hash it is bound into stays stable, and the
   * derived PQ public key is carried in the authorization so the verifier is
   * self-contained.
   *
   * `turnNonce` MUST be the nonce of the turn this action will ride
   * (`turn.nonce == agent.state.nonce()` at commit) — v3 binds it into the
   * signature, so a mismatched nonce fails verification at commit.
   *
   * STAGED: the node accepts this alongside the classical
   * {@link signActionClassical} shape today and fail-closes on a
   * present-but-invalid PQ half; whether the PQ half is *required* is gated
   * node-side by `TurnExecutor::require_pq` (default off). Signing hybrid by
   * default is what makes that flip a no-op for TS callers.
   */
  signAction(action: Action, federationId: Uint8Array, turnNonce: bigint | number): Action {
    const message = actionSigningMessage(action, federationId, turnNonce);
    const ed25519 = this.signBytes(message);
    const pq = this.mlDsaKey();
    return {
      ...action,
      authorization: {
        kind: "hybridSignature",
        ed25519,
        mlDsa: mlDsaSign(pq.secretKey, message),
        mlDsaPk: pq.publicKey,
      },
    };
  }

  /**
   * Sign an action with the LEGACY CLASSICAL (ed25519-only)
   * `Authorization::Signature` shape — mirror of Rust's
   * `AgentCipherclerk::sign_action_classical`.
   *
   * {@link signAction} emits the hybrid variant by default; this remains for
   * consumers that must produce the pre-hybrid wire shape (a verifier that
   * predates `Authorization::HybridSignature`). It is accepted by the node
   * only while `require_pq` is off — it is the shape that goes dark the day
   * that flag flips.
   */
  signActionClassical(
    action: Action,
    federationId: Uint8Array,
    turnNonce: bigint | number,
  ): Action {
    const message = actionSigningMessage(action, federationId, turnNonce);
    const sig = this.signBytes(message);
    return {
      ...action,
      authorization: { kind: "signature", r: sig.slice(0, 32), s: sig.slice(32, 64) },
    };
  }

  /**
   * Sign a turn's canonical `Turn::hash` (v3) and wrap it in the postcard
   * `SignedTurn` envelope the node's `/api/turns/submit-signed` ingress
   * verifies (signature over the hash; `turn.agent` must be this identity's
   * default cell).
   */
  signTurnEnvelope(turn: Turn): Uint8Array {
    const hash = turnHash(turn);
    const sig = this.signBytes(hash);
    return encodeSignedTurn(turn, sig, this.publicKey);
  }
}
