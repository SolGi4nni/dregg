/** Public, active Dregg identity exposed through the page provider.
 *
 * The resolver is deliberately independent of custody.  It accepts only the
 * active profile's 32-byte public key, and only while the clerk is unlocked;
 * secret keys, mnemonics, holding receipts and wallet-provider objects are
 * neither inputs nor outputs.
 */

export interface ActiveDreggIdentity {
  publicKeyHex: string;
  profileName?: string;
}

export interface ActiveIdentityStateView {
  locked: boolean;
  uninitialized?: boolean;
  needsPassphraseSetup?: boolean;
  publicKey: readonly number[];
  activeProfile: string;
  profiles: ReadonlyArray<{ name: string; publicKey: readonly number[] }>;
}

export type ActiveIdentityResolution =
  | { ok: true; identity: ActiveDreggIdentity }
  | { ok: false; error: string };

const PROFILE_NAME = /^[a-z0-9_-]{1,64}$/;
const PUBLIC_KEY_HEX = /^[0-9a-f]{64}$/;

export function parseActiveDreggIdentity(value: unknown): ActiveDreggIdentity | null {
  if (!value || typeof value !== "object" || Array.isArray(value)) return null;
  const row = value as Record<string, unknown>;
  const keys = Object.keys(row).sort().join(",");
  if (keys !== "publicKeyHex" && keys !== "profileName,publicKeyHex") return null;
  if (typeof row.publicKeyHex !== "string" || !PUBLIC_KEY_HEX.test(row.publicKeyHex)) return null;
  if (row.profileName !== undefined && (typeof row.profileName !== "string" || !PROFILE_NAME.test(row.profileName))) return null;
  return Object.freeze({
    publicKeyHex: row.publicKeyHex,
    ...(row.profileName !== undefined ? { profileName: row.profileName } : {}),
  });
}

function publicKeyHex(value: readonly number[]): string | null {
  if (!Array.isArray(value) || value.length !== 32 ||
      value.some((byte) => !Number.isInteger(byte) || byte < 0 || byte > 255)) return null;
  return value.map((byte) => byte.toString(16).padStart(2, "0")).join("");
}

export function resolveActiveDreggIdentity(state: ActiveIdentityStateView): ActiveIdentityResolution {
  if (state.uninitialized) return { ok: false, error: "No Dregg identity has been created." };
  if (state.locked) return { ok: false, error: "Cipherclerk is locked." };
  if (state.needsPassphraseSetup) {
    return { ok: false, error: "Set a cipherclerk passphrase before sharing the active identity." };
  }
  if (!PROFILE_NAME.test(state.activeProfile)) return { ok: false, error: "The active Dregg profile is invalid." };
  const profile = state.profiles.find((candidate) => candidate.name === state.activeProfile);
  if (!profile) return { ok: false, error: "No active Dregg profile is available." };
  const profileHex = publicKeyHex(profile.publicKey);
  const mirroredHex = publicKeyHex(state.publicKey);
  if (!profileHex || !mirroredHex || profileHex !== mirroredHex) {
    return { ok: false, error: "The active Dregg identity state is inconsistent." };
  }
  return {
    ok: true,
    identity: Object.freeze({ publicKeyHex: profileHex, profileName: profile.name }),
  };
}
