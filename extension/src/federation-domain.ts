/**
 * signTurnV3 federation-domain bridge — shared validation.
 *
 * The optional second argument to `dregg.signTurnV3(turnBytes, federationId)`
 * is the 32-byte federation id the v3 action signing message binds against
 * (`dregg-action-sig-v2` domain separation; see
 * `TurnExecutor::compute_signing_message`). Both the page bridge and the
 * background service worker validate through this ONE function so the checks
 * cannot drift: exact type, exact length (32), and every element an integer
 * in 0..=255. Validation happens BEFORE any signing; omission (undefined)
 * stays on the backward-compatible all-zero devnet/sim genesis domain.
 *
 * Spec: DreggCloud docs/OWNER-LIFECYCLE-BROWSER-SEAM.md.
 */

/**
 * The capability string DreggCloud requires before it will hand a nonzero
 * owner-lifecycle federation domain to a browser provider. Published on
 * `window.dregg.capabilities.signTurnV3FederationDomain` only because the
 * complete page → content → background → WASM path is installed.
 */
export const SIGN_TURN_V3_FEDERATION_DOMAIN_CAPABILITY =
  "dregg-sign-turn-v3-federation-domain/v1";

/** Federation domains are exactly this many bytes. */
export const FEDERATION_DOMAIN_LENGTH = 32;

/** Lowercase hex of the legacy all-zero (devnet/sim genesis) domain. */
export const ZERO_FEDERATION_DOMAIN_HEX = "00".repeat(FEDERATION_DOMAIN_LENGTH);

export type FederationDomainValidation =
  | { ok: true; bytes: Uint8Array; hex: string }
  | { ok: false; error: string };

/** Lowercase hex encoding (64 chars for a 32-byte domain). */
export function federationDomainHex(bytes: Uint8Array): string {
  let out = "";
  for (let i = 0; i < bytes.length; i++) {
    out += bytes[i].toString(16).padStart(2, "0");
  }
  return out;
}

/**
 * Validate a present federation-domain value with exact checks.
 *
 * Accepts a `Uint8Array` or a plain 32-entry byte array (the shape the value
 * takes after crossing the nonce-bound page message as `number[]`). Rejects
 * everything else: wrong type, wrong length (0/31/33/...), fractional,
 * negative, or >255 elements. On success returns a fresh COPY of the bytes
 * (so a caller-held reference mutated after validation cannot change what is
 * signed) plus the full 64-char lowercase hex.
 *
 * `undefined` is NOT handled here on purpose: absence is the caller's
 * backward-compatible zero-domain path, and only absence may default.
 */
export function validateFederationDomain(value: unknown): FederationDomainValidation {
  if (value instanceof Uint8Array) {
    if (value.length !== FEDERATION_DOMAIN_LENGTH) {
      return {
        ok: false,
        error: `federationId must be exactly ${FEDERATION_DOMAIN_LENGTH} bytes, got ${value.length}`,
      };
    }
    const bytes = new Uint8Array(value);
    return { ok: true, bytes, hex: federationDomainHex(bytes) };
  }
  if (Array.isArray(value)) {
    if (value.length !== FEDERATION_DOMAIN_LENGTH) {
      return {
        ok: false,
        error: `federationId must be exactly ${FEDERATION_DOMAIN_LENGTH} bytes, got ${value.length}`,
      };
    }
    const bytes = new Uint8Array(FEDERATION_DOMAIN_LENGTH);
    for (let i = 0; i < FEDERATION_DOMAIN_LENGTH; i++) {
      const b: unknown = value[i];
      if (typeof b !== "number" || !Number.isInteger(b) || b < 0 || b > 255) {
        return {
          ok: false,
          error: `federationId[${i}] must be an integer in 0..=255, got ${String(b)}`,
        };
      }
      bytes[i] = b;
    }
    return { ok: true, bytes, hex: federationDomainHex(bytes) };
  }
  return {
    ok: false,
    error: "federationId must be a Uint8Array (or 32-entry byte array)",
  };
}
