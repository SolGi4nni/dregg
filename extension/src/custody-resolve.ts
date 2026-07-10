/**
 * Custody RESOLUTION — the §4.5 honest chain that picks WHO signs a dregg turn,
 * so the sign+submit path is driven by a `CustodyProvider` rather than a hard-wired
 * key. This is the seam that lets an EXTENSION-LESS person sign with a passkey
 * (§4/§8: writes without lock-in).
 *
 * The chain, in order:
 *   1. extension-present (an unlocked signing key)  → the extension's own custody.
 *      Expressed as a `MnemonicCustody` (its mnemonic-derived key as a provider)
 *      when the recovery phrase is recoverable AND re-derives to the active
 *      identity — so the seam is provably byte-identical to today's direct path;
 *      otherwise a byte-exact `SeedCustody` over the already-unlocked seed (never
 *      depends on decrypting the phrase, e.g. a BIP39-passphrase wallet).
 *   2. else a `PasskeyCustody` if a passkey has been enrolled (the extension-less
 *      floor: a WebAuthn PRF-wrapped dregg key).
 *   3. else NO custody — read-only. Any write FAILS CLOSED (no provider to sign).
 *
 * The tier is surfaced so the UI/caller can be honest about the custody in force.
 */

import {
  CustodyProvider,
  CustodyWasm,
  MnemonicCustody,
  SeedCustody,
  bytesEqual,
  publicKeyFromMnemonic,
} from "./custody";
import { PasskeyCustody, CustodyStore } from "./passkey";

/** Which custody actually signs — surfaced so callers never sign blind about the tier. */
export type CustodyTier = "extension" | "passkey" | "none";

export interface ResolvedCustody {
  /** The provider that will sign, or `null` when there is no custody (fail-closed on writes). */
  provider: CustodyProvider | null;
  /** The honest custody tier in force. */
  tier: CustodyTier;
}

/** The extension's unlocked signing material (present only when the extension is unlocked). */
export interface ExtensionCustodyMaterial {
  /** The active profile's 32-byte ed25519 seed (the signing key). */
  secretKey: Uint8Array;
  /** The active profile's 32-byte ed25519 public key (the identity to bind to). */
  publicKey: Uint8Array;
  /**
   * Recover the active profile's recovery phrase + its BIP39 passphrase, if available.
   * Returning `null` (locked, absent, or a non-standard wallet) makes resolution fall
   * back to the byte-exact seed provider — signing never blocks on the phrase.
   */
  getMnemonic?: () => Promise<{ mnemonic: string; passphrase: string } | null>;
}

export interface CustodyEnv {
  /** dregg signing, reused wholesale by every provider. */
  wasm: CustodyWasm;
  /** The extension's own custody material, when the extension is present + unlocked. */
  extension?: ExtensionCustodyMaterial;
  /** Where a passkey enrollment lives (chrome.storage in the extension). */
  passkeyStore?: CustodyStore;
  /** The relying-party id a passkey is bound to (extension origin / host). */
  passkeyRpId?: string;
  /** Injected for testability; defaults to the ambient browser globals inside PasskeyCustody. */
  credentials?: CredentialsContainer;
  subtle?: SubtleCrypto;
}

/**
 * Resolve the active custody provider following the §4.5 chain. FAIL-CLOSED: when
 * no custody is available the result carries `provider: null` / `tier: "none"`, and
 * the caller MUST refuse any write.
 */
export async function resolveCustody(env: CustodyEnv): Promise<ResolvedCustody> {
  const ext = env.extension;
  if (ext && ext.secretKey.length === 32) {
    // Prefer the mnemonic-derived provider when the phrase re-derives to the SAME
    // identity (byte-identical to the direct path); else the byte-exact seed.
    if (ext.getMnemonic) {
      try {
        const m = await ext.getMnemonic();
        if (m) {
          const derivedPub = publicKeyFromMnemonic(env.wasm, m.mnemonic, m.passphrase);
          if (bytesEqual(derivedPub, ext.publicKey)) {
            return { provider: new MnemonicCustody(env.wasm, () => m), tier: "extension" };
          }
        }
      } catch {
        // A corrupt/undecryptable phrase must NEVER crash signing — fall through
        // to the byte-exact seed provider below.
      }
    }
    return {
      provider: new SeedCustody(env.wasm, ext.secretKey, ext.publicKey),
      tier: "extension",
    };
  }

  // Extension-less: a passkey, if one has been enrolled.
  if (env.passkeyStore) {
    const pk = new PasskeyCustody({
      wasm: env.wasm,
      store: env.passkeyStore,
      rpId: env.passkeyRpId,
      credentials: env.credentials,
      subtle: env.subtle,
    });
    if (await pk.isEnrolled()) {
      return { provider: pk, tier: "passkey" };
    }
  }

  // No custody at all — read-only. Any write fails closed.
  return { provider: null, tier: "none" };
}
