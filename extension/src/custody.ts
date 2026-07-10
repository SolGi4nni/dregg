/**
 * Pluggable CUSTODY abstraction — the "who holds the dregg signing key" seam.
 *
 * A dregg turn is authorized by a HYBRID ed25519 + ML-DSA-65 (FIPS 204)
 * signature: the SDK's `AgentCipherclerk::sign_turn` signs the canonical
 * `Turn::hash` with BOTH halves, derived from a single 32-byte seed, and
 * postcard-serializes `SignedTurn { turn, signature, signer, pq_signature,
 * pq_signer }`. The wasm exposes that WHOLESALE as
 * `assemble_signed_turn_envelope(turnBytes, senderPrivkey)`; the seed itself
 * comes from a BIP39 mnemonic via `derive_keypair_from_mnemonic`.
 *
 * dregg's crypto is UNCHANGED by anything in this file. A `CustodyProvider` is
 * key-*holding*, not a new signature scheme: it decides how the mnemonic/seed is
 * stored and gated, then hands the seed to the exact same wasm signing path the
 * background worker uses. The browser extension is one custody provider (it holds
 * a passphrase-locked mnemonic in worker memory); the WebAuthn passkey
 * (`./passkey`) is another (it wraps the mnemonic under a PRF-derived secret that
 * only the platform authenticator / biometric can reproduce). Both implement this
 * one interface, so a person can authorize a turn WITHOUT the extension —
 * sovereignty without lock-in.
 */

/**
 * An ArrayBuffer-backed byte array. WebCrypto (`crypto.subtle`) and WebAuthn
 * (`navigator.credentials`) accept `BufferSource`, which excludes the
 * `SharedArrayBuffer`-backed case; pinning to `ArrayBuffer` keeps every byte we
 * hand those APIs assignable without casts.
 */
export type Bytes = Uint8Array<ArrayBuffer>;

/** The narrow wasm surface a custody provider needs — dregg signing, reused wholesale. */
export interface CustodyWasm {
  /**
   * Derive the hybrid keypair from a BIP39 mnemonic. `secret_key` is the 32-byte
   * ed25519 seed the SDK expands into BOTH the ed25519 identity and the ML-DSA-65
   * key; `public_key` is the 32-byte ed25519 verifying key (the custody identity).
   * (`path` is accepted for signature-compatibility with the extension's call; the
   * derivation path is fixed inside the wasm.)
   */
  derive_keypair_from_mnemonic(
    mnemonic: string,
    passphrase: string,
    path: string,
  ): { public_key: Uint8Array; secret_key: Uint8Array };
  /**
   * Assemble the canonical HYBRID `SignedTurn` envelope (the exact postcard bytes
   * `/api/turns/submit-signed` decodes) from an encoded `Turn` and the 32-byte
   * ed25519 seed. Routes through `AgentCipherclerk::sign_turn` — the ed25519 AND
   * ML-DSA-65 halves ride end-to-end.
   */
  assemble_signed_turn_envelope(turnBytes: Uint8Array, senderPrivkey: Uint8Array): Uint8Array;
  /** Generate a fresh 24-word BIP39 mnemonic (optional; used when enrolling a new key). */
  generate_mnemonic?(): string;
  /** Validate a BIP39 mnemonic (optional; used to fail closed on a corrupt unwrap). */
  validate_mnemonic?(mnemonic: string): boolean;
}

/** The canonical HYBRID SignedTurn the node's `/api/turns/submit-signed` decodes. */
export interface SignedTurnEnvelope {
  /**
   * postcard-encoded `SignedTurn { turn, signature, signer, pq_signature,
   * pq_signer }` — ed25519 + ML-DSA-65 over the canonical `Turn::hash`. The exact
   * bytes to POST; the node re-derives `turn.hash()`, verifies the ed25519 half,
   * checks the PQ half fail-closed when present, and binds `turn.agent` to `signer`.
   */
  bytes: Uint8Array;
  /** the 32-byte ed25519 signer public key embedded in the envelope (the custody identity). */
  signer: Uint8Array;
}

/**
 * A custody provider: holds the dregg key and produces the hybrid SignedTurn.
 * The extension's built-in custody and the passkey both implement this — the port
 * wires whichever is present into its consent/custody seam.
 */
export interface CustodyProvider {
  /** Whether this provider can be used in the current context (API + material present). */
  isAvailable(): Promise<boolean>;
  /** The 32-byte ed25519 public key that will sign — safe to reveal without a gate. */
  publicKey(): Promise<Uint8Array>;
  /** Gate, unlock the key, and produce the hybrid SignedTurn. FAILS CLOSED on any denial. */
  signTurn(turnBytes: Uint8Array): Promise<SignedTurnEnvelope>;
  /** Human-readable name for UI ("Passkey", "Extension cipherclerk", …). */
  label(): string;
}

/** The wasm's fixed derivation path selector (ignored by the wasm; kept for parity). */
export const DREGG_KEY_PATH = "dregg/0";

/**
 * The single load-bearing signing step, shared by every provider: derive the
 * hybrid keypair from the mnemonic and assemble the canonical envelope. The seed
 * material exists ONLY transiently here and is zeroized before returning.
 */
export function signTurnWithMnemonic(
  wasm: CustodyWasm,
  mnemonic: string,
  passphrase: string,
  turnBytes: Uint8Array,
): SignedTurnEnvelope {
  const kp = wasm.derive_keypair_from_mnemonic(mnemonic, passphrase, DREGG_KEY_PATH);
  const secretKey = kp.secret_key;
  const signer = new Uint8Array(kp.public_key); // copy: the public half is the identity
  try {
    const bytes = wasm.assemble_signed_turn_envelope(turnBytes, secretKey);
    return { bytes, signer };
  } finally {
    zeroize(secretKey);
  }
}

/** Derive the hybrid public key (the custody identity) from a mnemonic. */
export function publicKeyFromMnemonic(
  wasm: CustodyWasm,
  mnemonic: string,
  passphrase: string,
): Uint8Array {
  const kp = wasm.derive_keypair_from_mnemonic(mnemonic, passphrase, DREGG_KEY_PATH);
  zeroize(kp.secret_key);
  return new Uint8Array(kp.public_key);
}

/** Best-effort scrub of secret bytes from the JS heap (the wasm scrubs its own linear memory). */
export function zeroize(...buffers: Array<Uint8Array | null | undefined>): void {
  for (const b of buffers) if (b) b.fill(0);
}

/** Normalize a WebAuthn/WebCrypto BufferSource to a Uint8Array. */
export function toBytes(src: BufferSource): Uint8Array {
  if (src instanceof Uint8Array) return src;
  if (src instanceof ArrayBuffer) return new Uint8Array(src);
  return new Uint8Array(src.buffer, src.byteOffset, src.byteLength);
}

/** Constant-time-ish equality for public byte arrays (identity checks, not secrets). */
export function bytesEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  let diff = 0;
  for (let i = 0; i < a.length; i++) diff |= a[i] ^ b[i];
  return diff === 0;
}

/**
 * Adapter sketch: the extension's EXISTING custody as a `CustodyProvider`.
 *
 * The shipping background worker already holds a passphrase-unlocked mnemonic and
 * signs via the same wasm path; this thin wrapper is what the port would wrap that
 * state in so the extension provider and the passkey provider are interchangeable.
 * Kept minimal on purpose — the passkey (`./passkey`) is the deliverable; this
 * shows the interface is genuinely pluggable and that dregg signing is shared, not
 * reimplemented.
 */
export class MnemonicCustody implements CustodyProvider {
  constructor(
    private readonly wasm: CustodyWasm,
    private readonly unlock: () => { mnemonic: string; passphrase: string } | null,
  ) {}

  async isAvailable(): Promise<boolean> {
    return this.unlock() !== null;
  }

  async publicKey(): Promise<Uint8Array> {
    const m = this.unlock();
    if (!m) throw new Error("custody locked: no unlocked mnemonic");
    return publicKeyFromMnemonic(this.wasm, m.mnemonic, m.passphrase);
  }

  async signTurn(turnBytes: Uint8Array): Promise<SignedTurnEnvelope> {
    const m = this.unlock();
    if (!m) throw new Error("custody locked: refusing to sign");
    return signTurnWithMnemonic(this.wasm, m.mnemonic, m.passphrase, turnBytes);
  }

  label(): string {
    return "Extension cipherclerk";
  }
}

/**
 * The extension's ALREADY-UNLOCKED 32-byte seed as a `CustodyProvider`.
 *
 * This is the exact operation the background worker performs today
 * (`assemble_signed_turn_envelope(turnBytes, secretKey)`), now expressed through
 * the interface — the extension holds the derived seed in worker memory, not the
 * mnemonic. It is BYTE-IDENTICAL to a `MnemonicCustody` over the same key: both
 * feed the same 32-byte seed to the same wasm signing path, so the mnemonic-derived
 * provider and this seed provider are two interchangeable expressions of the SAME
 * custody. Used when the extension has a derived key but the mnemonic is not
 * recoverable / does not re-derive to the active identity (e.g. a BIP39-passphrase
 * wallet), so signing never depends on decrypting the recovery phrase.
 */
export class SeedCustody implements CustodyProvider {
  private readonly seed: Uint8Array;
  private readonly signer: Uint8Array;

  /** `publicKey` is the 32-byte ed25519 identity this seed signs as (the extension already holds it). */
  constructor(
    private readonly wasm: CustodyWasm,
    seed: Uint8Array,
    publicKey: Uint8Array,
  ) {
    if (seed.length !== 32) throw new Error("SeedCustody: seed must be exactly 32 bytes");
    this.seed = new Uint8Array(seed); // copy: signing material, kept alive for the provider's life
    this.signer = new Uint8Array(publicKey);
  }

  async isAvailable(): Promise<boolean> {
    return this.seed.length === 32;
  }

  async publicKey(): Promise<Uint8Array> {
    return new Uint8Array(this.signer);
  }

  async signTurn(turnBytes: Uint8Array): Promise<SignedTurnEnvelope> {
    const bytes = this.wasm.assemble_signed_turn_envelope(turnBytes, this.seed);
    return { bytes, signer: new Uint8Array(this.signer) };
  }

  label(): string {
    return "Extension cipherclerk";
  }
}
