/**
 * identity.js — who you are in the shell.
 *
 * A profile is a named local keypair: a 24-word recovery phrase (entropy for
 * the dregg BLAKE3 derivation path — the wasm's `derive_keypair_from_mnemonic`
 * hashes the phrase string; it is NOT a BIP39-checksummed mnemonic), the
 * derived Ed25519 public key, and the hosted cell id the node derives from
 * that key (`CellId::derive_raw(pubkey, blake3("default"))`).
 *
 * Storage is plain localStorage, UNENCRYPTED — devnet-grade custody, stated
 * on the surface. Real custody is the Cipherclerk extension's job.
 *
 * Provisioning: POST /api/faucet with `public_key` so the node materializes a
 * canonical hosted cell under the profile's real key (a faucet cell without a
 * pubkey gets an all-zero key and can never pass turn signature checks).
 */

import { deriveCellIdHex, bytesToHex } from './blake3.js';

const PROFILES_KEY = 'starbridge.shell.profiles.v1';
const ACTIVE_KEY = 'starbridge.shell.activeProfile.v1';

// 256 words = 8 bits/word; 24 words = 192 bits of phrase entropy.
export const WORDLIST = (
  'acorn amber anchor apple arrow ash atlas autumn badge bagel bamboo barley basil beacon berry birch ' +
  'bison blaze bloom bluff board bonfire boots bramble brass bread breeze brick bridge brook bucket butter ' +
  'cabin cactus camp canoe canyon carbon cedar chalk cherry cinder citrus clay cliff clover cobalt comet ' +
  'compass copper coral cotton cove crane creek cricket crystal cumin current cypress daisy dawn delta dew ' +
  'dome drift dune dusk eagle earth echo ember falcon feather fern field fig finch fjord flint ' +
  'fog forest fossil fox frost galaxy garden garnet geyser ginger glacier glade glen gorge granite grape ' +
  'grove gull harbor hawk hazel heath heron hill hollow honey horizon ibis ice indigo inlet iris ' +
  'iron island ivory ivy jade jasper juniper kelp kestrel kite lagoon lake lantern larch lark lava ' +
  'leaf ledge lemon lichen lilac lily lime linen lotus lunar lynx maple marble marsh meadow mesa ' +
  'mint mist moss moth mountain mulberry myrtle nectar nest night north nutmeg oak oasis ocean olive ' +
  'onyx opal orchard osprey otter owl palm pearl pebble pepper petal pine plain plum pollen pond ' +
  'poplar prairie prism quail quartz quill rain raven reed ridge river robin rose rowan ruby rust ' +
  'saffron sage salt sand sapphire seal sedge shade shell shore silver sky slate snow solar sparrow ' +
  'spring spruce star stone storm stream summit sun swan tea teak tern thicket thorn thyme tide ' +
  'timber topaz torch trail trout tulip tundra turquoise valley vapor vine violet walnut water wave west ' +
  'wheat willow wind winter wolf wren yarrow yew zephyr zinc alder aspen bay briar elm hemlock'
).split(' ');

/** 24 words drawn with rejection-free uniform bytes (256 words exactly). */
export function generatePhrase() {
  const bytes = new Uint8Array(24);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (b) => WORDLIST[b]).join(' ');
}

export function loadProfiles() {
  try {
    const list = JSON.parse(localStorage.getItem(PROFILES_KEY) || '[]');
    return Array.isArray(list) ? list.filter((p) => p && p.id && p.publicKeyHex && p.cellId) : [];
  } catch {
    return [];
  }
}

function saveProfiles(profiles) {
  try { localStorage.setItem(PROFILES_KEY, JSON.stringify(profiles.slice(0, 16))); } catch {}
}

export function activeProfile() {
  const id = (() => {
    try { return localStorage.getItem(ACTIVE_KEY) || ''; } catch { return ''; }
  })();
  const profiles = loadProfiles();
  return profiles.find((p) => p.id === id) || null;
}

export function setActiveProfile(id) {
  try {
    if (id) localStorage.setItem(ACTIVE_KEY, id);
    else localStorage.removeItem(ACTIVE_KEY);
  } catch {}
}

function toByteArray(value) {
  if (value instanceof Uint8Array) return value;
  if (Array.isArray(value)) return Uint8Array.from(value);
  throw new Error('unexpected key encoding from wasm');
}

/**
 * Create (and persist + activate) a profile from a phrase. `wasm` is the
 * initialized dregg_wasm module — the keypair derivation is the same
 * BLAKE3-path the SDK and extension use.
 */
export function createProfile(wasm, { name, phrase }) {
  const words = String(phrase || '').trim().split(/\s+/);
  if (words.length !== 24) throw new Error(`a phrase is 24 words (got ${words.length})`);
  const normalized = words.join(' ');
  const keypair = wasm.derive_keypair_from_mnemonic(normalized, '');
  const publicKey = toByteArray(keypair.public_key);
  const profile = {
    id: `p-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 7)}`,
    name: String(name || '').trim() || 'sovereign',
    phrase: normalized,
    publicKeyHex: bytesToHex(publicKey),
    cellId: deriveCellIdHex(publicKey),
    createdAt: new Date().toISOString(),
  };
  const profiles = loadProfiles();
  profiles.unshift(profile);
  saveProfiles(profiles);
  setActiveProfile(profile.id);
  return profile;
}

export function forgetProfile(id) {
  saveProfiles(loadProfiles().filter((p) => p.id !== id));
  const active = (() => {
    try { return localStorage.getItem(ACTIVE_KEY); } catch { return null; }
  })();
  if (active === id) setActiveProfile(null);
}

/**
 * Claim devnet computrons for a profile's hosted cell. Materializes the cell
 * under the profile's real public key. Resolves
 * `{ ok, amount?, turnHash?, error? }`; a node without `--enable-faucet`
 * answers 404/405 — reported, never faked.
 */
export async function claimFaucet(baseUrl, profile, amount = 1000) {
  const base = String(baseUrl || '').replace(/\/+$/, '');
  try {
    const res = await fetch(`${base}/api/faucet`, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({
        recipient: profile.cellId,
        amount,
        public_key: profile.publicKeyHex,
      }),
    });
    if (!res.ok) {
      return { ok: false, error: `faucet HTTP ${res.status}${res.status === 404 ? ' (node runs without --enable-faucet)' : ''}` };
    }
    const data = await res.json();
    if (!data.success) return { ok: false, error: data.error || 'faucet rejected the request' };
    return { ok: true, amount: data.amount, turnHash: data.turn_hash || data.tx_hash };
  } catch (e) {
    return { ok: false, error: `faucet unreachable: ${e?.message || e}` };
  }
}
