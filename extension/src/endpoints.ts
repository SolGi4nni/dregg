/**
 * Central endpoint config for the Dragon's Egg cipherclerk extension.
 *
 * The dregg domains used to be hardcoded as string literals across the
 * extension (background worker, settings page, manifest). This module is the
 * single source for the bundled TS code; it defaults to the current product
 * `node.dregg.net` host and can be overridden at runtime via
 * `globalThis.__DREGG_ENDPOINTS__ = { devnet: "my.node.example" }` before the
 * worker reads the defaults.
 *
 * The prior default (`devnet.dregg.fg-goose.online`) was the retired devnet-era
 * domain; the product surface is `dregg.net`. A user still points the extension
 * at any node — their own localhost/tailnet node or a hosted one — through the
 * settings page; this is only the out-of-the-box default.
 *
 * NOTE: `manifest.json` host_permissions and the plain-JS `settings-script.js`
 * are separate static surfaces (a browser extension requires literal hosts in
 * the manifest); those carry their own copy of the host on purpose.
 */

/** The default product node host (no scheme). */
export const DEFAULT_DEVNET_DOMAIN = "node.dregg.net";

function devnetDomain(): string {
  const o = (globalThis as { __DREGG_ENDPOINTS__?: { devnet?: string } }).__DREGG_ENDPOINTS__;
  const v = o?.devnet;
  return v && v.trim() ? v.trim() : DEFAULT_DEVNET_DOMAIN;
}

/** `https://{devnet}` — the default node base URL. */
export function defaultNodeUrl(): string {
  return `https://${devnetDomain()}`;
}

/** `wss://{devnet}/ws` — the default node event-stream URL. */
export function defaultNodeWssUrl(): string {
  return `wss://${devnetDomain()}/ws`;
}
