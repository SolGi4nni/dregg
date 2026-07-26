/**
 * Dregg endpoints — the ONE source of truth for the production domains (TS side).
 *
 * Mirrors the Rust `dregg_sdk::endpoints` module. Historically these domains
 * were hardcoded as string literals across the SDK, the browser extension, the
 * playground, etc.; pointing at a new domain meant editing every literal. This
 * module centralizes them as distinct NAMED endpoints (they serve different
 * purposes and are not collapsed into one):
 *
 *   api      — the main / canonical API host        (dregg.net)
 *   devnet   — the public devnet node (HTTP + WSS)   (node.dregg.net)
 *   auth     — the auth / credential surface         (auth.dregg.net)
 *   gateway  — the macaroon discharge gateway        (gateway.dregg.net)
 *   hosting  — the WebOfCells cell-hosting wildcard  (dregg.works)
 *   portal   — the static portal / "live" view       (portal.dregg.studio)
 *
 * ⚠ MEASURED 2026-07-26 — THESE ARE NAMES, NOT LIVE SERVICE. Do not read this
 * table as "the defaults reach something". Probed from a laptop that day:
 *
 *   node.dregg.net, auth.dregg.net, gateway.dregg.net, dregg.works  → NXDOMAIN
 *   dregg.net                        → Squarespace, the marketing site, not an API
 *   portal.dregg.studio              → 34.224.208.52, the OLD AWS edge (static portal)
 *   devnet.dregg.fg-goose.online     → 34.224.208.52, TLS handshake FAILS (no cert)
 *
 * So there is no public dregg node to default to right now. These names are the
 * product family the Rust SDK already declares (`sdk/src/endpoints.rs`), and the
 * previous values here — the `*.dregg.fg-goose.online` devnet family — are the
 * RETIRED devnet-era domain on the AWS box being migrated off
 * (`~/dev/dregg-infra/edge/RUNBOOK.md`). Neither reaches a node; only one of them
 * is the name we intend to keep. Point the SDK at your own node.
 *
 * Overrides (so production is a config change, not 83 edits):
 *   - Node: the `DREGG_{API,DEVNET,AUTH,GATEWAY,HOSTING,PORTAL}_DOMAIN` env vars.
 *   - Browser: assign `globalThis.__DREGG_ENDPOINTS__ = { devnet: "..." , ... }`
 *     before constructing clients.
 *
 * This file is browser-safe: it never imports `fs`/`path` and only touches
 * `process.env` behind a guard, so it can be re-exported from `browser.ts`.
 */

/** The named dregg domains (bare hosts, no scheme). */
export interface DreggDomains {
  /** Main / canonical API host. */
  api: string;
  /** Public devnet node host (HTTP + WSS). */
  devnet: string;
  /** Auth / credential surface. */
  auth: string;
  /** Macaroon discharge gateway. */
  gateway: string;
  /** WebOfCells cell-hosting wildcard root. */
  hosting: string;
  /** Static portal / "live" network view. */
  portal: string;
}

/**
 * The product domain family (the baked-in defaults). Kept byte-identical to the
 * Rust `dregg_sdk::endpoints::defaults` so the two "one source of truth" modules
 * cannot disagree — they did, from the fg-goose retirement until 2026-07-26.
 *
 * See the module header: as of 2026-07-26 none of these serve a node.
 */
export const DEFAULT_DOMAINS: Readonly<DreggDomains> = Object.freeze({
  api: "dregg.net",
  devnet: "node.dregg.net",
  auth: "auth.dregg.net",
  gateway: "gateway.dregg.net",
  hosting: "dregg.works",
  portal: "portal.dregg.studio",
});

/** Map a domain field to its Node env-var name. */
const ENV_VARS: Record<keyof DreggDomains, string> = {
  api: "DREGG_API_DOMAIN",
  devnet: "DREGG_DEVNET_DOMAIN",
  auth: "DREGG_AUTH_DOMAIN",
  gateway: "DREGG_GATEWAY_DOMAIN",
  hosting: "DREGG_HOSTING_DOMAIN",
  portal: "DREGG_PORTAL_DOMAIN",
};

function envOverride(field: keyof DreggDomains): string | undefined {
  // Node only — guarded so this stays usable in a browser bundle.
  const env = (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env;
  const v = env?.[ENV_VARS[field]];
  return v && v.trim() ? v.trim() : undefined;
}

function browserOverride(field: keyof DreggDomains): string | undefined {
  const o = (globalThis as { __DREGG_ENDPOINTS__?: Partial<DreggDomains> }).__DREGG_ENDPOINTS__;
  const v = o?.[field];
  return v && v.trim() ? v.trim() : undefined;
}

/**
 * Resolve the live domains: per-field, a browser `__DREGG_ENDPOINTS__` override
 * wins, then a Node env var, else the production default. With nothing set this
 * equals {@link DEFAULT_DOMAINS}.
 */
export function resolveDomains(): DreggDomains {
  const out = {} as DreggDomains;
  for (const key of Object.keys(DEFAULT_DOMAINS) as (keyof DreggDomains)[]) {
    out[key] = browserOverride(key) ?? envOverride(key) ?? DEFAULT_DOMAINS[key];
  }
  return out;
}

/** `https://{devnet}` — the default node base URL an SDK client points at. */
export function devnetUrl(domains: DreggDomains = resolveDomains()): string {
  return `https://${domains.devnet}`;
}

/** `wss://{devnet}/ws` — the default node event-stream URL. */
export function devnetWssUrl(domains: DreggDomains = resolveDomains()): string {
  return `wss://${domains.devnet}/ws`;
}

/** `https://{api}` — the canonical API base URL. */
export function apiUrl(domains: DreggDomains = resolveDomains()): string {
  return `https://${domains.api}`;
}

/** `https://{gateway}` — the macaroon discharge gateway base URL. */
export function gatewayUrl(domains: DreggDomains = resolveDomains()): string {
  return `https://${domains.gateway}`;
}

/** `https://{portal}` — the static portal base URL. */
export function portalUrl(domains: DreggDomains = resolveDomains()): string {
  return `https://${domains.portal}`;
}

/**
 * The resolved endpoint URLs, computed once at import. Use the `*Url` functions
 * instead when you need to honor a `globalThis.__DREGG_ENDPOINTS__` override set
 * after import.
 */
export const DREGG_ENDPOINTS = Object.freeze({
  /** Default node URL (e.g. `https://node.dregg.net`). */
  defaultNodeUrl: devnetUrl(),
  /** Default node WSS URL (e.g. `wss://node.dregg.net/ws`). */
  defaultNodeWssUrl: devnetWssUrl(),
});
