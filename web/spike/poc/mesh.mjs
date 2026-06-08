// mesh.mjs — the in-browser dregg node's connection to the REAL mesh.
//
// This is the honest, capability-aware client the browser participant uses to
// talk to a live dregg node over its HTTP API (node/src/api.rs). It is NOT a
// mock: every call here hits the configured endpoint (devnet by default) and
// returns the node's real response (or a real error).
//
// What a browser CAN do against the live mesh, and what it CANNOT:
//
//   * READ-SYNC (real, works): /status, /api/federations, /api/blocks,
//     /api/receipts, /api/cells, /api/tokens, /api/intents. These are the
//     blocklace/federation/ledger projections the node serves. The browser
//     pulls them to learn the live mesh state (DAG height, block count,
//     consensus liveness, federation roots) — i.e. it SYNCS blocklace-derived
//     state over the API relay.
//
//   * LOCAL-VERIFY (real, works): once synced, the browser re-runs candidate
//     turns through the *verified* Lean executor compiled to wasm
//     (execFullForestG / dregg_exec_full_forest_auth) and checks the
//     commit/rollback verdict itself — no trust in the node for the verdict.
//
//   * SUBMIT (API-relayed, best-effort): /turn/submit relays a signed turn to
//     the node for inclusion. This sits behind the node's require_auth bearer
//     gate, so an anonymous browser submission is expected to be rejected
//     (401) unless an operator token is supplied. We attempt it and report the
//     REAL outcome rather than pretending success.
//
//   * FULL GOSSIP (NOT feasible in-page): the node's peer-to-peer blocklace
//     gossip is a libp2p/QUIC transport with no browser binding. A page cannot
//     join the gossip mesh directly; it participates via the API relay above.
//     We are explicit about this rather than implying the browser is a full
//     gossip peer.

export const DEFAULT_ENDPOINT = "https://devnet.dregg.fg-goose.online";

// Resolve the endpoint: ?endpoint= query param overrides the default so the
// page points at any node (local dev node, a chosen devnet peer, etc).
export function resolveEndpoint(search) {
  try {
    const p = new URLSearchParams(search || "");
    const e = p.get("endpoint");
    if (e) return e.replace(/\/+$/, "");
  } catch {}
  return DEFAULT_ENDPOINT;
}

// A fetch with a hard timeout (the live devnet backend can wedge/GC-pause; we
// must surface that as a real, bounded error instead of hanging the page).
async function fetchT(url, opts = {}, ms = 8000) {
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), ms);
  const t0 = (typeof performance !== "undefined" ? performance.now() : Date.now());
  try {
    const res = await fetch(url, { ...opts, signal: ctrl.signal });
    const ms_ = ((typeof performance !== "undefined" ? performance.now() : Date.now()) - t0);
    return { res, ms: ms_ };
  } finally {
    clearTimeout(t);
  }
}

// GET a JSON endpoint; returns {ok, status, json, ms, error}. Never throws.
async function getJson(endpoint, path, ms = 8000) {
  try {
    const { res, ms: dt } = await fetchT(endpoint + path, { headers: { accept: "application/json" } }, ms);
    let json = null, text = null;
    try { json = await res.clone().json(); } catch { try { text = await res.text(); } catch {} }
    return { ok: res.ok, status: res.status, json, text, ms: Math.round(dt), error: null };
  } catch (e) {
    return { ok: false, status: 0, json: null, text: null, ms: ms, error: String(e && e.name === "AbortError" ? "timeout" : e) };
  }
}

// ---- READ-SYNC surface -----------------------------------------------------

// Pull the node's live status: the canonical mesh heartbeat. Fields (real,
// from node/src/api.rs get_status): healthy, peer_count, latest_height,
// dag_height, block_count, consensus_live, revocation_count, note_count,
// federation_mode, public_key.
export function getStatus(endpoint, ms = 8000) {
  return getJson(endpoint, "/status", ms);
}

// Federation roots: the committee/epoch/threshold + latest_root the node has
// finalized. This is the blocklace-anchored federation projection.
export function getFederations(endpoint, ms = 8000) {
  return getJson(endpoint, "/api/federations", ms);
}

// Ledger projections the node serves (blocks / receipts / cells / tokens /
// intents). Each is an array; on a fresh devnet they are commonly empty but
// the 200 + array shape is real.
export function getBlocks(endpoint, ms = 8000)   { return getJson(endpoint, "/api/blocks", ms); }
export function getReceipts(endpoint, ms = 8000) { return getJson(endpoint, "/api/receipts", ms); }
export function getCells(endpoint, ms = 8000)    { return getJson(endpoint, "/api/cells", ms); }
export function getTokens(endpoint, ms = 8000)   { return getJson(endpoint, "/api/tokens", ms); }
export function getIntents(endpoint, ms = 8000)  { return getJson(endpoint, "/api/intents", ms); }

// Snapshot = one round of read-sync. Runs the reads concurrently and folds
// them into a single mesh view, recording per-endpoint reachability so the UI
// can be honest about what synced and what didn't.
export async function syncSnapshot(endpoint, ms = 8000) {
  const [status, feds, blocks, receipts, cells, tokens, intents] = await Promise.all([
    getStatus(endpoint, ms), getFederations(endpoint, ms), getBlocks(endpoint, ms),
    getReceipts(endpoint, ms), getCells(endpoint, ms), getTokens(endpoint, ms),
    getIntents(endpoint, ms),
  ]);
  const reach = { status, feds, blocks, receipts, cells, tokens, intents };
  const reachable = Object.values(reach).filter(r => r.ok).length;
  return {
    endpoint,
    at: new Date().toISOString(),
    reachable,                       // how many of the 7 reads succeeded
    total: 7,
    online: status.ok === true,      // node API responding at all
    status: status.json,
    federations: feds.json,
    counts: {
      blocks: Array.isArray(blocks.json) ? blocks.json.length : null,
      receipts: Array.isArray(receipts.json) ? receipts.json.length : null,
      cells: Array.isArray(cells.json) ? cells.json.length : null,
      tokens: Array.isArray(tokens.json) ? tokens.json.length : null,
      intents: Array.isArray(intents.json) ? intents.json.length : null,
    },
    reach,                           // raw per-endpoint {ok,status,ms,error}
  };
}

// ---- SUBMIT surface (API-relayed, best-effort) -----------------------------

// A node-shaped `/turn/submit` body (SubmitTurnRequest in node/src/api.rs).
// The node signs as ITSELF (operator cipherclerk) — `agent` is advisory only
// (confused-deputy hardening F-P1-3), so a browser cannot impersonate a cell.
// We send the most innocuous real effect: bump the operator cell's nonce.
// This is a genuinely well-formed turn; whether it COMMITS depends on the
// node's auth/unlock state (403 locked / 401 devnet-auth), which is the point.
export function sampleNodeTurn() {
  return {
    agent: "0".repeat(64),
    nonce: 0,
    fee: 0,
    memo: "in-browser node hello",
    actions: [{ method: "submit", effects: [{ kind: "increment_nonce" }] }],
  };
}

// Relay a signed turn to the node for inclusion. `bearer` (optional) is the
// operator API token; without it the node's require_auth gate is expected to
// answer 401/403 — which we report honestly as "rejected by auth gate", not a
// failure of the browser node. Returns {ok, status, json, error, relayed}.
export async function submitTurn(endpoint, turnWire, bearer = null, ms = 12000) {
  const headers = { "content-type": "application/json" };
  if (bearer) headers["authorization"] = "Bearer " + bearer;
  try {
    const { res, ms: dt } = await fetchT(endpoint + "/turn/submit", {
      method: "POST", headers,
      body: typeof turnWire === "string" ? turnWire : JSON.stringify(turnWire),
    }, ms);
    let json = null; try { json = await res.clone().json(); } catch {}
    return {
      relayed: true,
      ok: res.ok,
      status: res.status,
      authGated: res.status === 401 || res.status === 403,
      json,
      ms: Math.round(dt),
      error: null,
    };
  } catch (e) {
    return { relayed: false, ok: false, status: 0, authGated: false, json: null,
             ms, error: String(e && e.name === "AbortError" ? "timeout" : e) };
  }
}

// A static, honest description of the browser node's mesh capabilities — used
// by the UI so we never overclaim. Pure data; no network.
export const CAPABILITIES = Object.freeze({
  readSync:    { real: true,  via: "node HTTP API (/status, /api/*)", note: "blocklace/federation/ledger projections, polled" },
  localVerify: { real: true,  via: "wasm execFullForestG (dregg_exec_full_forest_auth)", note: "the proved gated complete-turn executor, run client-side" },
  submit:      { real: "best-effort", via: "POST /turn/submit (API relay)", note: "behind node require_auth bearer gate; anonymous submit expected 401" },
  gossip:      { real: false, via: "libp2p/QUIC blocklace gossip", note: "no browser transport binding; participation is via the API relay, not direct gossip" },
});
