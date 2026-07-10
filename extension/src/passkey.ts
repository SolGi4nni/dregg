/**
 * PasskeyCustody — an extension-less custody floor (§4/§8: "sovereignty without
 * lock-in"). A person authorizes a dregg turn with a WebAuthn passkey — a
 * platform authenticator / biometric — and NO browser extension.
 *
 * THE MODEL (the passkey WRAPS/UNLOCKS the dregg key; it is NOT the signature):
 * WebAuthn assertions are ES256/EdDSA and CANNOT be an ML-DSA cap signature, so a
 * passkey assertion is never the turn signature. Instead:
 *
 *   enroll:  register a passkey with the WebAuthn **PRF** extension (hmac-secret)
 *            → PRF-derive a stable 32-byte wrapping secret (gated by the
 *            authenticator) → HKDF → AES-256-GCM-wrap the dregg BIP39 mnemonic
 *            under it → store { credentialId, wrappedSeed, publicKey }.
 *   sign:    authenticate the passkey (PRF) → re-derive the wrap secret →
 *            AES-GCM-unwrap the mnemonic → `derive_keypair_from_mnemonic` →
 *            `assemble_signed_turn_envelope` → the HYBRID SignedTurn. The seed
 *            exists only transiently in memory, gated by the authenticator, and is
 *            zeroized after signing.
 *
 * dregg's hybrid crypto is UNCHANGED — this reuses the exact wasm signing path
 * (`../custody`.signTurnWithMnemonic). FAIL-CLOSED everywhere: no PRF support, a
 * failed assertion, or a failed unwrap yields NO signature (never a weak-KDF
 * fallback). The wrapped ciphertext alone (without the authenticator) cannot sign.
 */

import {
  Bytes,
  CustodyProvider,
  CustodyWasm,
  SignedTurnEnvelope,
  signTurnWithMnemonic,
  toBytes,
  zeroize,
} from "./custody";

/** AES-GCM-wrapped seed material: the ciphertext + its nonce. Holds NO plaintext. */
export interface WrappedSeed {
  /** 12-byte AES-GCM nonce. */
  iv: Bytes;
  /** AES-256-GCM ciphertext (mnemonic UTF-8 bytes + 16-byte tag). */
  ciphertext: Bytes;
}

/** The persisted passkey enrollment. Everything here is safe at rest WITHOUT the authenticator. */
export interface PasskeyEnrollment {
  /** Raw WebAuthn credential id (the handle presented to `navigator.credentials.get`). */
  credentialId: Bytes;
  /** The mnemonic, AES-GCM-wrapped under the PRF-derived secret. */
  wrappedSeed: WrappedSeed;
  /** The 32-byte ed25519 public key (public identity — cached so `publicKey()` needs no gate). */
  publicKey: Bytes;
  /** The relying-party id the credential is bound to. */
  rpId: string;
  createdAt: number;
}

/** Persistence seam for the enrollment (chrome.storage in the extension; in-memory in tests). */
export interface CustodyStore {
  load(): Promise<PasskeyEnrollment | null>;
  save(enrollment: PasskeyEnrollment): Promise<void>;
  clear(): Promise<void>;
}

export interface PasskeyCustodyDeps {
  /** dregg signing, reused wholesale. */
  wasm: CustodyWasm;
  /** Where the enrollment blob lives. */
  store: CustodyStore;
  /** Relying-party id (defaults to `location.hostname`). */
  rpId?: string;
  rpName?: string;
  userName?: string;
  userDisplayName?: string;
  /** BIP39 passphrase for the wrapped mnemonic (defaults to ""). */
  passphrase?: string;
  /** Injected for testability; default to the ambient browser globals. */
  credentials?: CredentialsContainer;
  subtle?: SubtleCrypto;
  randomBytes?: (n: number) => Bytes;
}

/**
 * The fixed PRF evaluation input. PRF output = HMAC(credential-bound-key, salt),
 * so a constant salt makes the wrap secret STABLE across enroll and every sign for
 * a given credential, while remaining bound to (and inextricable from) that
 * authenticator. Domain-separated by an app-specific context string.
 */
const PRF_SALT_CONTEXT = "dregg-passkey-custody/prf-eval/v1";
/** HKDF info binding the derived AES key to this exact use. */
const HKDF_INFO = "dregg-passkey-custody/aes-256-gcm-seed-wrap/v1";

// ---------------------------------------------------------------------------
// Pure wrap/unwrap logic (no WebAuthn) — the security-relevant core, unit-testable
// with an injected PRF secret when a virtual authenticator cannot produce one.
// ---------------------------------------------------------------------------

/** The constant 32-byte PRF salt (SHA-256 of the context string). */
export async function prfSalt(subtle: SubtleCrypto): Promise<Bytes> {
  const digest = await subtle.digest("SHA-256", new TextEncoder().encode(PRF_SALT_CONTEXT));
  return new Uint8Array(digest);
}

/** HKDF-SHA256 the 32-byte PRF secret into a non-extractable AES-256-GCM key. */
async function deriveWrapKey(subtle: SubtleCrypto, prfSecret: Bytes): Promise<CryptoKey> {
  const ikm = await subtle.importKey("raw", prfSecret, "HKDF", false, ["deriveKey"]);
  return subtle.deriveKey(
    {
      name: "HKDF",
      hash: "SHA-256",
      salt: new Uint8Array(0),
      info: new TextEncoder().encode(HKDF_INFO),
    },
    ikm,
    { name: "AES-GCM", length: 256 },
    false,
    ["encrypt", "decrypt"],
  );
}

/** AES-GCM-wrap seed bytes under the PRF secret. Returns a blob holding NO plaintext. */
export async function wrapSeed(
  subtle: SubtleCrypto,
  prfSecret: Bytes,
  seed: Bytes,
  randomBytes: (n: number) => Bytes,
): Promise<WrappedSeed> {
  const key = await deriveWrapKey(subtle, prfSecret);
  const iv = randomBytes(12);
  const ct = await subtle.encrypt({ name: "AES-GCM", iv }, key, seed);
  return { iv, ciphertext: new Uint8Array(ct) };
}

/**
 * AES-GCM-unwrap. FAILS CLOSED: a wrong PRF secret or tampered ciphertext throws
 * (GCM tag mismatch) rather than returning garbage. Caller MUST zeroize the result.
 */
export async function unwrapSeed(
  subtle: SubtleCrypto,
  prfSecret: Bytes,
  wrapped: WrappedSeed,
): Promise<Bytes> {
  const key = await deriveWrapKey(subtle, prfSecret);
  let pt: ArrayBuffer;
  try {
    pt = await subtle.decrypt({ name: "AES-GCM", iv: wrapped.iv }, key, wrapped.ciphertext);
  } catch {
    throw new Error("passkey custody: seed unwrap failed (wrong authenticator or tampered blob)");
  }
  return new Uint8Array(pt);
}

// ---------------------------------------------------------------------------
// PasskeyCustody
// ---------------------------------------------------------------------------

export class PasskeyCustody implements CustodyProvider {
  private readonly wasm: CustodyWasm;
  private readonly store: CustodyStore;
  private readonly credentials: CredentialsContainer;
  private readonly subtle: SubtleCrypto;
  private readonly randomBytes: (n: number) => Bytes;
  private readonly rpId: string;
  private readonly rpName: string;
  private readonly userName: string;
  private readonly userDisplayName: string;
  private readonly passphrase: string;

  constructor(deps: PasskeyCustodyDeps) {
    this.wasm = deps.wasm;
    this.store = deps.store;
    const cred = deps.credentials ?? (globalThis.navigator && navigator.credentials);
    if (!cred) throw new Error("passkey custody: WebAuthn (navigator.credentials) unavailable");
    this.credentials = cred;
    this.subtle = deps.subtle ?? (globalThis.crypto && crypto.subtle);
    if (!this.subtle) throw new Error("passkey custody: WebCrypto (crypto.subtle) unavailable");
    this.randomBytes =
      deps.randomBytes ?? ((n: number) => crypto.getRandomValues(new Uint8Array(n)));
    this.rpId =
      deps.rpId ?? (typeof location !== "undefined" ? location.hostname : "");
    this.rpName = deps.rpName ?? "dregg";
    this.userName = deps.userName ?? "dregg custody";
    this.userDisplayName = deps.userDisplayName ?? "dregg custody";
    this.passphrase = deps.passphrase ?? "";
  }

  label(): string {
    return "Passkey";
  }

  /** WebAuthn + WebCrypto present. (PRF support can only be confirmed against a live credential.) */
  async isAvailable(): Promise<boolean> {
    return (
      typeof PublicKeyCredential !== "undefined" &&
      typeof this.credentials?.create === "function" &&
      typeof this.credentials?.get === "function" &&
      !!this.subtle
    );
  }

  /** Cached public identity — no authenticator gate needed for a public value. */
  async publicKey(): Promise<Uint8Array> {
    const e = await this.store.load();
    if (!e) throw new Error("passkey custody: not enrolled");
    return new Uint8Array(e.publicKey);
  }

  /** Whether an enrollment exists (a passkey has been bound to a dregg key). */
  async isEnrolled(): Promise<boolean> {
    return (await this.store.load()) !== null;
  }

  /**
   * Register a passkey and bind it to a dregg key.
   *
   * @param mnemonicSeed OPTIONAL UTF-8 bytes of a BIP39 mnemonic to adopt. Omit to
   *   generate a fresh key via the wasm. (The wrapped material is the mnemonic; the
   *   32-byte seed it expands to lives only transiently during signing.)
   */
  async enroll(mnemonicSeed?: Uint8Array): Promise<{ credentialId: Uint8Array; wrappedSeed: WrappedSeed }> {
    // 1. Obtain the mnemonic to protect (fresh, or the caller's), and its public identity.
    const mnemonicBytes = mnemonicSeed ? new Uint8Array(mnemonicSeed) : this.freshMnemonicBytes();
    const mnemonic = new TextDecoder().decode(mnemonicBytes);
    if (this.wasm.validate_mnemonic && !this.wasm.validate_mnemonic(mnemonic)) {
      zeroize(mnemonicBytes);
      throw new Error("passkey custody: refusing to enroll an invalid BIP39 mnemonic");
    }
    const kp = this.wasm.derive_keypair_from_mnemonic(mnemonic, this.passphrase, "dregg/0");
    const publicKey = new Uint8Array(kp.public_key);
    zeroize(kp.secret_key);

    // 2. Register the credential with PRF enabled. pubKeyCredParams cover the
    //    credential's own signature (ES256 / EdDSA) — irrelevant to the wrap.
    const created = (await this.credentials.create({
      publicKey: {
        challenge: this.randomBytes(32),
        rp: { id: this.rpId || undefined, name: this.rpName },
        user: { id: this.randomBytes(16), name: this.userName, displayName: this.userDisplayName },
        pubKeyCredParams: [
          { type: "public-key", alg: -8 }, // EdDSA
          { type: "public-key", alg: -7 }, // ES256
        ],
        authenticatorSelection: {
          residentKey: "required",
          requireResidentKey: true,
          userVerification: "required",
        },
        timeout: 60_000,
        attestation: "none",
        extensions: { prf: {} },
      },
    })) as PublicKeyCredential | null;
    if (!created) {
      zeroize(mnemonicBytes);
      throw new Error("passkey custody: credential creation returned null (cancelled)");
    }
    const credentialId = new Uint8Array(created.rawId);
    const ext = created.getClientExtensionResults();
    if (!ext.prf || ext.prf.enabled !== true) {
      // FAIL CLOSED: no PRF ⇒ no authenticator-gated wrap secret ⇒ refuse. No weak KDF.
      zeroize(mnemonicBytes);
      throw new Error(
        "passkey custody: authenticator does not support the WebAuthn PRF extension; refusing (no weak-KDF fallback)",
      );
    }

    // 3. Evaluate the PRF (gated assertion) → wrap secret → AES-GCM-wrap the mnemonic.
    const prfSecret = await this.evaluatePrf(credentialId);
    const wrappedSeed = await wrapSeed(this.subtle, prfSecret, mnemonicBytes, this.randomBytes);
    zeroize(prfSecret, mnemonicBytes);

    const enrollment: PasskeyEnrollment = {
      credentialId,
      wrappedSeed,
      publicKey,
      rpId: this.rpId,
      createdAt: Date.now(),
    };
    await this.store.save(enrollment);
    return { credentialId, wrappedSeed };
  }

  /**
   * Gate the passkey, unwrap the seed, and produce the HYBRID SignedTurn.
   * FAILS CLOSED on a missing enrollment, a failed/denied assertion, an
   * authenticator without the credential, or a failed unwrap — NO signature.
   */
  async signTurn(turnBytes: Uint8Array): Promise<SignedTurnEnvelope> {
    const e = await this.store.load();
    if (!e) throw new Error("passkey custody: not enrolled — refusing to sign");

    // 1. Authenticate (PRF). A wrong authenticator / denied UV throws here.
    const prfSecret = await this.evaluatePrf(e.credentialId);

    // 2. Unwrap the mnemonic (GCM tag fails closed on the wrong secret).
    let mnemonicBytes: Uint8Array | null = null;
    try {
      mnemonicBytes = await unwrapSeed(this.subtle, prfSecret, e.wrappedSeed);
      const mnemonic = new TextDecoder().decode(mnemonicBytes);
      // 3. Re-derive the hybrid key and assemble the envelope — the seed is
      //    transient and zeroized inside signTurnWithMnemonic.
      return signTurnWithMnemonic(this.wasm, mnemonic, this.passphrase, turnBytes);
    } finally {
      zeroize(prfSecret, mnemonicBytes);
    }
  }

  /**
   * Drive a gated WebAuthn assertion and read the PRF output as the 32-byte wrap
   * secret. FAILS CLOSED if the assertion fails or returns no PRF result.
   */
  private async evaluatePrf(credentialId: Bytes): Promise<Bytes> {
    const salt = await prfSalt(this.subtle);
    let assertion: PublicKeyCredential | null;
    try {
      assertion = (await this.credentials.get({
        publicKey: {
          challenge: this.randomBytes(32),
          rpId: this.rpId || undefined,
          allowCredentials: [{ type: "public-key", id: credentialId }],
          userVerification: "required",
          timeout: 60_000,
          extensions: { prf: { eval: { first: salt } } },
        },
      })) as PublicKeyCredential | null;
    } catch (err) {
      throw new Error(
        `passkey custody: authentication failed (${(err as Error).message || err}) — refusing to sign`,
      );
    }
    if (!assertion) throw new Error("passkey custody: authentication cancelled — refusing to sign");
    const prf = assertion.getClientExtensionResults().prf;
    if (!prf || !prf.results || !prf.results.first) {
      throw new Error("passkey custody: no PRF result from authenticator — refusing to sign");
    }
    const secret = toBytes(prf.results.first);
    if (secret.length < 32) {
      throw new Error("passkey custody: PRF result too short — refusing to sign");
    }
    return new Uint8Array(secret.slice(0, 32));
  }

  private freshMnemonicBytes(): Bytes {
    if (!this.wasm.generate_mnemonic) {
      throw new Error("passkey custody: wasm.generate_mnemonic unavailable; pass a mnemonicSeed");
    }
    return new TextEncoder().encode(this.wasm.generate_mnemonic());
  }
}

// ---------------------------------------------------------------------------
// chrome.storage-backed store (the extension wiring; not used in the page test)
// ---------------------------------------------------------------------------

const STORE_KEY = "dregg_passkey_custody_v1";

/** Enrollment persisted in `chrome.storage.local` (bytes as base64 for JSON transport). */
export class ChromeCustodyStore implements CustodyStore {
  constructor(private readonly key: string = STORE_KEY) {}

  async load(): Promise<PasskeyEnrollment | null> {
    const got = await chrome.storage.local.get(this.key);
    const raw = got[this.key];
    if (!raw || typeof raw !== "object") return null;
    return {
      credentialId: b64ToBytes(raw.credentialId),
      wrappedSeed: { iv: b64ToBytes(raw.wrappedSeed.iv), ciphertext: b64ToBytes(raw.wrappedSeed.ciphertext) },
      publicKey: b64ToBytes(raw.publicKey),
      rpId: raw.rpId,
      createdAt: raw.createdAt,
    };
  }

  async save(e: PasskeyEnrollment): Promise<void> {
    await chrome.storage.local.set({
      [this.key]: {
        credentialId: bytesToB64(e.credentialId),
        wrappedSeed: { iv: bytesToB64(e.wrappedSeed.iv), ciphertext: bytesToB64(e.wrappedSeed.ciphertext) },
        publicKey: bytesToB64(e.publicKey),
        rpId: e.rpId,
        createdAt: e.createdAt,
      },
    });
  }

  async clear(): Promise<void> {
    await chrome.storage.local.remove(this.key);
  }
}

/** In-memory store for tests / ephemeral sessions. */
export class InMemoryCustodyStore implements CustodyStore {
  private enrollment: PasskeyEnrollment | null = null;
  async load(): Promise<PasskeyEnrollment | null> {
    return this.enrollment;
  }
  async save(e: PasskeyEnrollment): Promise<void> {
    this.enrollment = e;
  }
  async clear(): Promise<void> {
    this.enrollment = null;
  }
}

function bytesToB64(b: Uint8Array): string {
  let s = "";
  for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]);
  return btoa(s);
}
function b64ToBytes(s: string): Bytes {
  const bin = atob(s);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}
