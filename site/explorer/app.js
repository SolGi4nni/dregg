/**
 * dregg explorer — inspector-substrate shell.
 *
 * The explorer is the SAME inspectors as the Studio/Playground, over a live
 * federation node instead of an in-browser wasm runtime. We mount a single
 * <dregg-app> whose `.runtime` is a read-only RemoteRuntime, then render every
 * object view through the platform <dregg-*> inspectors (STUDIO.md § 3, § 5).
 *
 * There is NO bespoke node viewer here and NO fabricated data: when the node is
 * unreachable the inspectors render their own honest empty states and the
 * connection chrome says "offline". When connected, every pixel is real node
 * data resolved through a real inspector via dregg:// URIs.
 *
 *   search/nav  ──▶  dregg:// URI  ──▶  <dregg-KIND uri="...">  (inside <dregg-app>)
 */

import { createRemoteRuntime } from '../_includes/studio/runtime-remote.js';
import { createNodeLink } from '../_includes/studio/shell/node-link.js';
import { parseRef, isRef } from '../_includes/studio/uri.js';
import { classifyConstraints, constraintsOf } from '../_includes/studio/polis-decode.js';
// Side-effect import: registers every <dregg-*> inspector custom element and
// the <dregg-app> context provider. This is the platform vocabulary.
import '../_includes/studio/context.js';
import '../_includes/studio/inspectors.js';

const NODE_URL_KEY = 'dregg_node_url';
const DEFAULT_NODE_URL = 'http://localhost:8420'; // local-dev fallback
const AUTO_REFRESH_KEY = 'dregg_auto_refresh';

// ---------------------------------------------------------------------------
// Node URL config (localStorage).
// ---------------------------------------------------------------------------
// When the explorer is served from a real (non-localhost) host — e.g. the devnet
// behind Caddy at devnet.dregg.fg-goose.online — default to that SAME ORIGIN.
// Same-origin avoids mixed-content (the old http://localhost default is blocked
// from an https page) and CORS; Caddy fronts /status, /api/*, /ws on that origin.
// Local dev (file:// or a localhost host) still falls back to localhost:8420,
// and an explicit user setting in localStorage always wins.
function defaultNodeUrl() {
  try {
    const { protocol, hostname, origin } = window.location;
    const isLocal = hostname === 'localhost' || hostname === '127.0.0.1' || hostname === '[::1]';
    if ((protocol === 'http:' || protocol === 'https:') && !isLocal) return origin;
  } catch (_) { /* non-browser context */ }
  return DEFAULT_NODE_URL;
}
export function getNodeUrl() {
  return localStorage.getItem(NODE_URL_KEY) || defaultNodeUrl();
}
export function setNodeUrl(url) {
  localStorage.setItem(NODE_URL_KEY, String(url || '').trim());
}

// ---------------------------------------------------------------------------
// Nav pages → the inspector (and URI) each one mounts.
//
// "list" pages mount a collection inspector against the live runtime; "object"
// pages are reached by search/deep-link and mount a single-object inspector.
// Every tag here is a platform-level <dregg-*> element (STUDIO.md § 5).
// ---------------------------------------------------------------------------
const PAGES = {
  overview:     { kind: 'overview' },
  blocks:       { tag: 'dregg-block-dag',    uri: () => 'dregg://block-dag/0' },
  cells:        { tag: 'dregg-cell-list',    uri: () => 'dregg://cell-list/all' },
  receipts:     { tag: 'dregg-receipt-list', uri: () => 'dregg://receipt-list/all' },
  turns:        { tag: 'dregg-receipt-list', uri: () => 'dregg://receipt-list/all' },
  history:      { custom: 'history' },
  polis:        { custom: 'polis' },
  capabilities: { tag: 'dregg-capability-list', uri: () => 'dregg://capability-list/0' },
  intents:      { custom: 'intents' },
  federation:   { tag: 'dregg-federation-list', uri: () => 'dregg://federation-list/all' },
  activity:     { tag: 'dregg-activity',     uri: () => 'dregg://activity/feed' },
};

// Map a parsed dregg:// kind to the nav page that hosts its inspector.
const KIND_TO_PAGE = {
  'cell-history': 'history',
  council: 'polis',
  constitution: 'polis',
  mandate: 'polis',
  'amendment-ceremony': 'polis',
  cell: 'cells',
  receipt: 'receipts',
  turn: 'turns',
  block: 'blocks',
  'block-dag': 'blocks',
  federation: 'federation',
  'federation-list': 'federation',
  capability: 'capabilities',
  'capability-list': 'capabilities',
  token: 'capabilities',
  intent: 'intents',
  'intent-list': 'intents',
  activity: 'activity',
};

// Some dregg:// kinds alias to a different inspector element.
const INSPECTOR_ALIASES = {
  token: 'attenuated-token',
  // A single receipt opens the unified witnessed view: it embeds <dregg-receipt>
  // + <dregg-proof> AND renders the real DWR1 witness artifacts that
  // RemoteRuntime lazy-fetches from /api/receipts/{hash}/witnesses (F1). The
  // receipt-list and turn views are unaffected (different kinds).
  receipt: 'witnessed-receipt',
};

// ---------------------------------------------------------------------------
// Module state.
// ---------------------------------------------------------------------------
let runtime = null;
let api = null;            // window.dreggUi (Preact + signals)
let appEl = null;          // the single <dregg-app>
let currentPage = 'overview';
let connected = false;
let livenessTimer = null;
let sampleMode = false;    // OPT-IN labeled sample snapshot (devnet unreachable)
let everConnected = false;
let nodeLink = null;       // shell node-link: SSE receipt stream + poll fallback

function latestHeight() {
  try {
    const blocks = runtime?.listBlocks?.().value || [];
    return blocks.reduce((max, b) => Math.max(max, Number(b.height ?? b.block_height ?? 0)), 0);
  } catch { return 0; }
}

// First strictly-positive finite number among the candidates, else 0. Used to
// pick the most meaningful height field a node exposes (linear or DAG).
function firstPositive(...vals) {
  for (const v of vals) {
    const n = Number(v);
    if (Number.isFinite(n) && n > 0) return n;
  }
  return 0;
}

function whenDreggUi() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

// ---------------------------------------------------------------------------
// Connection indicator + liveness.
// ---------------------------------------------------------------------------
function setConnection(state) {
  const el = document.getElementById('connection-status');
  if (!el) return;
  el.classList.remove('connected', 'error', 'sample');
  const label = el.querySelector('.ex-connection__label');
  if (state === 'connected') {
    el.classList.add('connected');
    if (label) label.textContent = 'connected';
  } else if (state === 'connecting') {
    if (label) label.textContent = 'connecting…';
  } else if (state === 'sample') {
    el.classList.add('sample');
    if (label) label.textContent = 'SAMPLE DATA';
  } else {
    el.classList.add('error');
    if (label) label.textContent = 'offline';
  }
  connected = state === 'connected';
  if (connected) everConnected = true;
  updateSampleBanner(state);
}

// ---------------------------------------------------------------------------
// Sample mode: clearly-labeled offline fallback. The banner appears when the
// node is unreachable; entering sample mode is a USER ACTION (never a silent
// substitution) and the chrome stays loudly labeled the whole time.
// ---------------------------------------------------------------------------
function updateSampleBanner(state) {
  const banner = document.getElementById('sample-banner');
  if (!banner) return;
  const text = document.getElementById('sample-banner-text');
  const enter = document.getElementById('sample-enter-btn');
  const exit = document.getElementById('sample-exit-btn');
  if (sampleMode) {
    banner.hidden = false;
    banner.classList.add('is-sample');
    if (text) text.innerHTML =
      '<strong>SAMPLE MODE</strong> — everything below is a static, labeled snapshot. ' +
      'Nothing comes from a node.';
    if (enter) enter.hidden = true;
    if (exit) exit.hidden = false;
  } else if (state === 'offline' || state === 'error') {
    banner.hidden = false;
    banner.classList.remove('is-sample');
    if (enter) enter.hidden = false;
    if (exit) exit.hidden = true;
  } else {
    banner.hidden = true;
  }
}

async function enterSampleMode() {
  const { createSampleRuntime } = await import('./sample-data.js');
  if (runtime && runtime.destroy) { try { runtime.destroy(); } catch {} }
  stopLiveness();
  stopReceiptStream();
  sampleMode = true;
  paintReceiptStream(null); // honest "no live stream" label
  runtime = createSampleRuntime({ signals: api });
  if (appEl) appEl.runtime = runtime;
  setConnection('sample');
  const metaEl = document.getElementById('devnet-node-meta');
  const urlEl = document.getElementById('devnet-node-url');
  if (urlEl) urlEl.textContent = 'SAMPLE SNAPSHOT (no node)';
  if (metaEl) metaEl.textContent = 'static labeled sample — not live data';
  // Remount the current page against the sample runtime.
  document.querySelectorAll('.ex-page .ex-detail-slot').forEach((d) => d.replaceChildren());
  remountAll();
  navigateTo(currentPage);
}

async function exitSampleMode() {
  sampleMode = false;
  setConnection('connecting');
  await buildRuntime();
  startLiveness();
  startReceiptStream();
  document.querySelectorAll('.ex-page .ex-detail-slot').forEach((d) => d.replaceChildren());
  remountAll();
  navigateTo(currentPage);
}

// Force list-page inspectors + overview tiles to remount against the current
// runtime (they read `.runtime` from <dregg-app> at mount time).
function remountAll() {
  const grid = document.getElementById('overview-inspectors');
  if (grid) { grid.dataset.mounted = 'false'; grid.replaceChildren(); }
  document.querySelectorAll('[id^="mount-"]').forEach((m) => m.replaceChildren());
}

/**
 * Probe /status directly for an honest connected/offline signal that is
 * independent of whether any particular object exists. RemoteRuntime polls in
 * the background; this is just for the chrome indicator. No fabricated data —
 * a failed probe shows "offline".
 */
async function probeLiveness() {
  if (sampleMode) return; // chrome stays loudly SAMPLE until the user exits
  const base = getNodeUrl().replace(/\/+$/, '');
  const probe = (path, ms = 6000) => {
    const ctl = new AbortController();
    const t = setTimeout(() => ctl.abort(), ms);
    return fetch(`${base}${path}`, { headers: { Accept: 'application/json' }, signal: ctl.signal })
      .finally(() => clearTimeout(t));
  };
  try {
    const res = await probe('/status');
    setConnection(res.ok ? 'connected' : 'offline');
    if (res.ok) {
      const status = await res.json().catch(() => null);
      updateStatusChrome(status);
      return;
    }
  } catch { /* fall through to the cheap-route fallback */ }
  // /status can be slow on a busy node (it walks the DAG); a cheap API route
  // is still an honest liveness signal — connected, but without status meta.
  try {
    const res = await probe('/api/cells', 6000);
    if (res.ok) {
      setConnection('connected');
      const metaEl = document.getElementById('devnet-node-meta');
      if (metaEl) metaEl.textContent = 'connected (status endpoint slow — height unavailable)';
      return;
    }
  } catch { /* genuinely unreachable */ }
  setConnection('offline');
  updateStatusChrome(null);
}

function updateStatusChrome(status) {
  const heightEl = document.getElementById('nav-height-value');
  const urlEl = document.getElementById('devnet-node-url');
  const metaEl = document.getElementById('devnet-node-meta');
  if (urlEl) urlEl.textContent = getNodeUrl();
  if (!status) {
    if (heightEl) heightEl.textContent = '--';
    if (metaEl) metaEl.textContent = connected ? 'connected' : 'not connected';
    return;
  }
  // dregg runs DAG consensus (Cordial-Miners), so a solo/DAG node reports its
  // progress as `dag_height`/`block_count` while the linear `latest_height`
  // stays 0. Fall back through the DAG fields so a live node shows its real
  // height instead of a misleading 0.
  const h = firstPositive(
    status.latest_height, status.height, status.block_height,
    status.dag_height, status.block_count,
  );
  if (heightEl) heightEl.textContent = String(h);
  if (metaEl) {
    const mode = status.federation_mode || (status.healthy ? 'healthy' : 'responding');
    const live = status.consensus_live ? ' · consensus live' : '';
    metaEl.textContent = `${mode} · height ${h} · ${status.peer_count ?? 0} peer(s)${live}`;
  }
}

function autoRefreshEnabled() {
  return localStorage.getItem(AUTO_REFRESH_KEY) !== 'false';
}

function startLiveness() {
  stopLiveness();
  probeLiveness();
  if (autoRefreshEnabled()) {
    livenessTimer = setInterval(probeLiveness, 5000);
  }
}
function stopLiveness() {
  if (livenessTimer) { clearInterval(livenessTimer); livenessTimer = null; }
}

// ---------------------------------------------------------------------------
// Receipt stream — the SAME node link the Starbridge shell uses
// (_includes/studio/shell/node-link.js): SSE on /api/events/stream with
// Last-Event-ID resume, honest poll fallback on /api/events, and a surfaced
// mode so the badge never claims a fabricated "live". Rows cross-link into
// the platform inspectors via the existing data-dregg-uri click delegation.
// ---------------------------------------------------------------------------
const STREAM_MODE_LABEL = {
  sse: 'live · SSE',
  poll: 'polling /api/events',
  off: 'no stream',
  sample: 'sample mode — no live stream',
};

function paintReceiptStream(state) {
  const modeEl = document.getElementById('receipt-stream-mode');
  const listEl = document.getElementById('receipt-stream-list');
  if (!modeEl || !listEl) return;
  const mode = sampleMode ? 'sample' : (state?.streamMode || 'off');
  modeEl.textContent = STREAM_MODE_LABEL[mode] || mode;
  modeEl.dataset.mode = mode;

  const events = sampleMode ? [] : (state?.events || []);
  listEl.replaceChildren();
  if (!events.length) {
    const li = document.createElement('li');
    li.className = 'ex-receipt-stream__empty';
    li.textContent = sampleMode
      ? 'Sample mode is a static snapshot — there is no live stream to show.'
      : (mode === 'off'
        ? 'No event stream from this node (endpoint unreachable). The list fills as soon as the SSE stream or the poll fallback connects.'
        : 'Connected — waiting for the first committed turn.');
    listEl.appendChild(li);
    return;
  }
  for (const ev of events.slice(0, 12)) {
    const li = document.createElement('li');
    li.className = 'ex-receipt-stream__row';
    const receiptUri = `dregg://receipt/${ev.receiptHash || ev.turnHash}`;
    const cellLinks = ev.cells.slice(0, 3).map((c) =>
      `<a data-dregg-uri="dregg://cell/${escapeHtml(c)}" href="?at=${encodeURIComponent(`dregg://cell/${c}`)}"><code>${escapeHtml(String(c).slice(0, 10))}…</code></a>`
    ).join(' ');
    li.innerHTML =
      `<span class="ex-receipt-stream__height">#${escapeHtml(String(ev.height || '?'))}</span>` +
      `<a class="ex-receipt-stream__hash" data-dregg-uri="${escapeHtml(receiptUri)}" ` +
        `href="?at=${encodeURIComponent(receiptUri)}" title="${escapeHtml(ev.turnHash)}">` +
        `<code>${escapeHtml(String(ev.turnHash).slice(0, 16))}…</code></a>` +
      `<span class="ex-receipt-stream__kinds">${escapeHtml((ev.kinds || []).slice(0, 4).join(' · ') || 'turn')}</span>` +
      `<span class="ex-receipt-stream__cells">${cellLinks}</span>` +
      `<span class="ex-receipt-stream__proof" data-proved="${ev.hasProof ? 'yes' : 'no'}">` +
        `${ev.hasProof ? 'proof ✓' : 'no proof yet'}</span>`;
    listEl.appendChild(li);
  }
}

function stopReceiptStream() {
  if (nodeLink) { try { nodeLink.stop(); } catch {} nodeLink = null; }
}

function startReceiptStream() {
  stopReceiptStream();
  if (sampleMode) { paintReceiptStream(null); return; }
  nodeLink = createNodeLink(getNodeUrl());
  nodeLink.onChange(paintReceiptStream);
  nodeLink.start();
  paintReceiptStream(nodeLink.state);
}

// ---------------------------------------------------------------------------
// Runtime lifecycle.
// ---------------------------------------------------------------------------
async function buildRuntime() {
  if (runtime && runtime.destroy) {
    try { runtime.destroy(); } catch {}
  }
  runtime = await createRemoteRuntime({ signals: api, baseUrl: getNodeUrl() });
  if (appEl) appEl.runtime = runtime;
  return runtime;
}

// ---------------------------------------------------------------------------
// Inspector mounting. Every object view is a platform <dregg-*> element placed
// inside the shared <dregg-app>, so it resolves through the RemoteRuntime.
// ---------------------------------------------------------------------------
function mountInspector(container, uri) {
  container.replaceChildren();
  let parsed = null;
  try { parsed = parseRef(uri); } catch {}
  if (!parsed) {
    container.appendChild(emptyNotice('Bad object reference', uri));
    return;
  }
  const kind = INSPECTOR_ALIASES[parsed.kind] || parsed.kind;
  const tag = `dregg-${kind}`;
  if (!customElements.get(tag)) {
    container.appendChild(emptyNotice(`No inspector registered for "${parsed.kind}"`, uri));
    return;
  }
  const el = document.createElement(tag);
  el.setAttribute('uri', kind === parsed.kind ? uri : `dregg://${kind}/${parsed.id}`);
  container.appendChild(el);
}

function emptyNotice(title, detail) {
  const div = document.createElement('div');
  div.className = 'ex-inspector-empty';
  div.innerHTML = `<strong>${escapeHtml(title)}</strong>${detail ? `<code>${escapeHtml(detail)}</code>` : ''}`;
  return div;
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

// ---------------------------------------------------------------------------
// Routing / navigation.
// ---------------------------------------------------------------------------
export function navigateTo(page) {
  if (!PAGES[page]) page = 'overview';
  currentPage = page;

  document.querySelectorAll('.ex-nav__item').forEach(el => el.classList.remove('active'));
  const navItem = document.querySelector(`[data-page="${page}"]`);
  if (navItem) navItem.classList.add('active');

  document.querySelectorAll('.ex-page').forEach(el => el.classList.remove('active'));
  const pageEl = document.getElementById(`page-${page}`);
  if (pageEl) pageEl.classList.add('active');

  if (page === 'overview') { renderOverview(); return; }

  const def = PAGES[page];
  const mount = document.getElementById(`mount-${page}`);
  if (!mount) return;
  if (def.custom === 'intents') { renderIntentList(mount); return; }
  if (def.custom === 'history') { renderHistoryPage(); return; }
  if (def.custom === 'polis') { renderPolisPage(); return; }
  if (def.uri) mountInspector(mount, def.uri());
}

/**
 * Open a dregg:// URI: switch to the hosting page and mount the single-object
 * inspector in that page's detail slot. Sharable via ?at=.
 */
function openUri(uri) {
  let parsed;
  try { parsed = parseRef(uri); } catch { return false; }
  const page = KIND_TO_PAGE[parsed.kind] || 'overview';
  navigateTo(page);
  const detail = document.getElementById(`detail-${page}`) || document.getElementById(`mount-${page}`);
  if (detail) {
    mountInspector(detail, uri);
    detail.scrollIntoView?.({ behavior: 'smooth', block: 'start' });
  }
  writeAt(uri);
  return true;
}

function writeAt(uri) {
  const p = new URLSearchParams(window.location.search);
  if (uri) p.set('at', uri); else p.delete('at');
  const q = p.toString();
  window.history.replaceState(null, '', window.location.pathname + (q ? '?' + q : ''));
}

// ---------------------------------------------------------------------------
// Search: resolve free-text to a dregg:// URI.
//   - a full dregg:// URI passes through
//   - 64-hex → try cell, then receipt (whichever the runtime resolves)
//   - bare integer → block height
//   - "block/<h>", "cell/<id>", "receipt/<h>", "intent/<id>" shorthand
// ---------------------------------------------------------------------------
function resolveSearch(raw) {
  const q = String(raw || '').trim();
  if (!q) return null;
  if (isRef(q)) return q;

  const shorthand = /^(cell|receipt|turn|block|intent|federation|capability|token|history|council|constitution|mandate|ceremony)\/(.+)$/i.exec(q);
  if (shorthand) {
    const kind = shorthand[1].toLowerCase();
    const id = shorthand[2];
    if (kind === 'block') return `dregg://block/0/${id}`;
    if (kind === 'history') return `dregg://cell-history/${id}`;
    if (kind === 'ceremony') return `dregg://amendment-ceremony/${id}`;
    return `dregg://${kind}/${id}`;
  }

  if (/^\d+$/.test(q)) return `dregg://block/0/${q}`;          // block height
  if (/^[0-9a-f]{64}$/i.test(q)) return resolveHash(q);         // cell or receipt hash
  if (/^[0-9a-f]{6,}$/i.test(q)) return resolveHash(q);
  return null;
}

// A 32-byte hash can be a cell id, a receipt/turn hash, or an intent id. Prefer
// whichever the live runtime actually has; default to cell.
function resolveHash(hash) {
  try {
    const cells = runtime?.listCells?.().value || [];
    if (cells.some(c => String(c.cell_id || c.id || '').toLowerCase() === hash.toLowerCase())) {
      return `dregg://cell/${hash}`;
    }
    const receipts = runtime?.listReceipts?.().value || [];
    if (receipts.some(r => [r.turn_hash, r.receipt_hash, r.hash].some(h => String(h || '').toLowerCase() === hash.toLowerCase()))) {
      return `dregg://receipt/${hash}`;
    }
    const intents = runtime?.listIntents?.().value || [];
    if (intents.some(i => String(i.intent_id || i.id || '').toLowerCase() === hash.toLowerCase())) {
      return `dregg://intent/${hash}`;
    }
  } catch {}
  return `dregg://cell/${hash}`;
}

// ---------------------------------------------------------------------------
// Time travel: cell picker + <dregg-cell-history> mount. The datalist is fed
// live from the runtime's cell list; entering a 64-hex id works regardless.
// ---------------------------------------------------------------------------
function renderHistoryPage() {
  const input = document.getElementById('history-cell-input');
  const datalist = document.getElementById('history-cell-options');
  const btn = document.getElementById('history-walk-btn');
  if (!input || !btn) return;

  // Refresh the known-cells datalist from the live runtime.
  if (datalist) {
    datalist.replaceChildren();
    try {
      const cells = runtime?.listCells?.().value || [];
      for (const c of cells.slice(0, 60)) {
        const id = c.cell_id || c.id;
        if (!id) continue;
        const opt = document.createElement('option');
        opt.value = id;
        opt.label = `${String(id).slice(0, 16)}… (balance ${c.balance ?? '?'})`;
        datalist.appendChild(opt);
      }
    } catch {}
  }

  if (btn.dataset.wired !== 'true') {
    btn.dataset.wired = 'true';
    const walk = () => {
      const id = (input.value || '').trim().toLowerCase();
      if (!/^[0-9a-f]{6,64}$/.test(id)) {
        input.classList.add('is-bad');
        setTimeout(() => input.classList.remove('is-bad'), 1200);
        return;
      }
      openUri(`dregg://cell-history/${id}`);
    };
    btn.addEventListener('click', walk);
    input.addEventListener('keydown', (e) => { if (e.key === 'Enter') walk(); });
  }
}

// ---------------------------------------------------------------------------
// Polis: governance-cell inspection. The scan classifies the runtime's cells
// by their SERVED program views (polis-decode.js — the same recognizer the
// inspectors use); manual entry auto-detects the family at open time. Cells
// whose program view the node doesn't serve simply can't be classified —
// stated, not guessed.
// ---------------------------------------------------------------------------
const POLIS_TAG = {
  council: 'dregg-council',
  amendment: 'dregg-council',
  constitution: 'dregg-constitution',
  mandate: 'dregg-mandate',
};
const POLIS_KIND = { council: 'council', amendment: 'council', constitution: 'constitution', mandate: 'mandate' };

function classifyCellFamily(cell) {
  try {
    const cls = classifyConstraints(constraintsOf(cell?.program));
    return cls?.family || null;
  } catch { return null; }
}

async function openPolisCell(id) {
  // Auto-detect the family from the live cell's program view, then open the
  // right inspector. Unclassifiable → council view with its honest
  // "not council-shaped" label (the slots still render, labeled best-effort).
  let family = null;
  try {
    const sig = runtime?.getCell?.(id);
    let cell = sig?.value;
    if (!cell) {
      // give the lazy fetch one short beat
      await new Promise((r) => setTimeout(r, 600));
      cell = sig?.value;
    }
    family = classifyCellFamily(cell);
  } catch {}
  openUri(`dregg://${POLIS_KIND[family] || 'council'}/${id}`);
}

function renderPolisPage() {
  const input = document.getElementById('polis-cell-input');
  const datalist = document.getElementById('polis-cell-options');
  const btn = document.getElementById('polis-inspect-btn');
  const scan = document.getElementById('polis-scan');
  if (!input || !btn) return;

  // Scan the runtime's cell list for polis-shaped programs (only cells whose
  // list entry carries a program view are classifiable from the list).
  const cells = (() => { try { return runtime?.listCells?.().value || []; } catch { return []; } })();
  if (datalist) {
    datalist.replaceChildren();
    for (const c of cells.slice(0, 60)) {
      const id = c.cell_id || c.id;
      if (!id) continue;
      const opt = document.createElement('option');
      opt.value = id;
      const fam = classifyCellFamily(c);
      opt.label = `${String(id).slice(0, 16)}…${fam ? ` (${fam})` : ''}`;
      datalist.appendChild(opt);
    }
  }
  if (scan) {
    const found = cells
      .map((c) => ({ id: c.cell_id || c.id, family: classifyCellFamily(c) }))
      .filter((x) => x.id && x.family);
    if (found.length) {
      scan.innerHTML = `<div class="ex-page__header"><p>polis-shaped programs on this runtime:</p></div>`;
      const wrap = document.createElement('div');
      wrap.className = 'ex-polis-scan__chips';
      for (const f of found.slice(0, 24)) {
        const b = document.createElement('button');
        b.className = 'btn btn-secondary';
        b.textContent = `${f.family} ${String(f.id).slice(0, 12)}…`;
        b.addEventListener('click', () => openUri(`dregg://${POLIS_KIND[f.family]}/${f.id}`));
        wrap.appendChild(b);
      }
      scan.appendChild(wrap);
    } else {
      scan.innerHTML = `<div class="ex-inspector-empty"><strong>No polis-shaped cells classifiable from this runtime's cell list.</strong>` +
        `<span>Cells whose list entries carry no program view cannot be classified here — enter a cell id above ` +
        `(the inspector fetches its full program), or deploy a council from the Studio's worked examples.</span></div>`;
    }
  }

  if (btn.dataset.wired !== 'true') {
    btn.dataset.wired = 'true';
    const go = () => {
      const id = (input.value || '').trim().toLowerCase();
      if (!/^[0-9a-f]{6,64}$/.test(id)) {
        input.classList.add('is-bad');
        setTimeout(() => input.classList.remove('is-bad'), 1200);
        return;
      }
      openPolisCell(id);
    };
    btn.addEventListener('click', go);
    input.addEventListener('keydown', (e) => { if (e.key === 'Enter') go(); });
  }
}

function runSearch(raw) {
  const uri = resolveSearch(raw);
  const errEl = document.getElementById('search-error');
  if (!uri) {
    if (errEl) {
      errEl.textContent = `Could not resolve "${raw}". Try a cell id, receipt hash, block height, or dregg:// URI.`;
      errEl.hidden = false;
    }
    return;
  }
  if (errEl) errEl.hidden = true;
  openUri(uri);
}

// ---------------------------------------------------------------------------
// Overview: a live dashboard built entirely from runtime list inspectors.
// No bespoke rendering of node internals — just inspector tiles.
// ---------------------------------------------------------------------------
function renderOverview() {
  const grid = document.getElementById('overview-inspectors');
  if (!grid || grid.dataset.mounted === 'true') return;
  grid.dataset.mounted = 'true';
  const tiles = [
    { title: 'Cells', tag: 'dregg-cell-list', uri: 'dregg://cell-list/all' },
    { title: 'Receipts', tag: 'dregg-receipt-list', uri: 'dregg://receipt-list/all' },
    { title: 'Federations', tag: 'dregg-federation-list', uri: 'dregg://federation-list/all' },
    { title: 'Activity', tag: 'dregg-activity', uri: 'dregg://activity/feed' },
  ];
  for (const t of tiles) {
    const card = document.createElement('div');
    card.className = 'overview-panel';
    const head = document.createElement('div');
    head.className = 'overview-panel__header';
    head.innerHTML = `<h3>${escapeHtml(t.title)}</h3>`;
    const body = document.createElement('div');
    body.className = 'overview-panel__body';
    card.append(head, body);
    grid.appendChild(card);
    mountInspector(body, t.uri);
  }
}

// ---------------------------------------------------------------------------
// Intents: no platform list-inspector exists for intents, so this page is
// search/nav chrome — a live (signals-backed) index of the runtime's intent
// pool, each entry opening the platform <dregg-intent> inspector. The actual
// object view is still a real inspector over real node data.
// ---------------------------------------------------------------------------
function renderIntentList(mount) {
  mount.replaceChildren();
  const list = document.createElement('div');
  list.className = 'ex-intent-index';
  mount.appendChild(list);
  const detail = document.getElementById('detail-intents');

  const sig = runtime?.listIntents?.();
  const paint = () => {
    const intents = (sig?.value) || [];
    list.replaceChildren();
    if (!intents.length) {
      list.appendChild(emptyNotice('No intents in the node pool', connected ? '' : 'not connected'));
      return;
    }
    for (const intent of intents) {
      const id = intent.intent_id || intent.id || '';
      const row = document.createElement('button');
      row.type = 'button';
      row.className = 'ex-intent-index__row';
      row.innerHTML = `<span>${escapeHtml(intent.kind || 'intent')}</span><code>${escapeHtml(String(id).slice(0, 24))}</code>`;
      row.addEventListener('click', () => {
        if (detail) mountInspector(detail, `dregg://intent/${id}`);
        writeAt(`dregg://intent/${id}`);
      });
      list.appendChild(row);
    }
  };
  // Live: re-paint on every runtime signal change.
  if (api?.effect && sig) {
    api.effect(() => { sig.value; paint(); });
  } else {
    paint();
  }
}

// ---------------------------------------------------------------------------
// Wire chrome: nav, search, settings, deep-link handling.
// ---------------------------------------------------------------------------
function wireChrome() {
  document.querySelectorAll('.ex-nav__item').forEach(btn => {
    btn.addEventListener('click', () => navigateTo(btn.dataset.page));
  });
  document.querySelectorAll('[data-map-page]').forEach(btn => {
    btn.addEventListener('click', () => navigateTo(btn.dataset.mapPage));
  });

  const search = document.getElementById('search-input');
  if (search) {
    search.addEventListener('keydown', e => {
      if (e.key === 'Enter') runSearch(search.value);
    });
    document.addEventListener('keydown', e => {
      if (e.key === '/' && document.activeElement !== search) {
        e.preventDefault();
        search.focus();
      }
    });
  }

  // Delegate clicks on inspector-emitted dregg:// links to in-app navigation.
  document.addEventListener('click', e => {
    const link = e.target.closest('[data-dregg-uri], a[href*="?at=dregg"]');
    if (!link) return;
    const uri = link.getAttribute('data-dregg-uri')
      || new URLSearchParams(new URL(link.href, window.location.origin).search).get('at');
    if (uri && isRef(uri)) {
      e.preventDefault();
      openUri(uri);
    }
  });

  // Sample-mode banner buttons (offline fallback — opt-in, loudly labeled).
  document.getElementById('sample-enter-btn')?.addEventListener('click', () => {
    enterSampleMode().catch((e) => console.error('[explorer] sample mode failed', e));
  });
  document.getElementById('sample-exit-btn')?.addEventListener('click', () => {
    exitSampleMode().catch((e) => console.error('[explorer] reconnect failed', e));
  });

  wireSettings();
}

function wireSettings() {
  const btn = document.getElementById('settings-btn');
  const modal = document.getElementById('settings-modal');
  const urlInput = document.getElementById('node-url-input');
  const autoToggle = document.getElementById('auto-refresh-toggle');
  const save = document.getElementById('settings-save');
  const cancel = document.getElementById('settings-cancel');
  const test = document.getElementById('settings-test');
  if (!modal) return;

  const open = () => {
    if (urlInput) urlInput.value = getNodeUrl();
    if (autoToggle) autoToggle.checked = autoRefreshEnabled();
    modal.hidden = false;
  };
  const close = () => { modal.hidden = true; };

  btn?.addEventListener('click', open);
  cancel?.addEventListener('click', close);
  modal.querySelector('.ex-modal__backdrop')?.addEventListener('click', close);

  test?.addEventListener('click', async () => {
    const url = (urlInput?.value || '').trim().replace(/\/+$/, '');
    const msg = document.getElementById('diag-message');
    if (msg) msg.textContent = 'Probing…';
    try {
      const res = await fetch(`${url}/status`, { headers: { Accept: 'application/json' } });
      if (msg) msg.textContent = res.ok ? `OK (HTTP ${res.status})` : `HTTP ${res.status}`;
    } catch (err) {
      if (msg) msg.textContent = `Unreachable: ${err?.message || err} (CORS or offline — node allows only localhost/extension origins by default)`;
    }
  });

  save?.addEventListener('click', async () => {
    if (urlInput) setNodeUrl(urlInput.value);
    if (autoToggle) localStorage.setItem(AUTO_REFRESH_KEY, autoToggle.checked ? 'true' : 'false');
    close();
    sampleMode = false; // saving a node URL always returns to live mode
    setConnection('connecting');
    await buildRuntime();
    startLiveness();
    startReceiptStream();
    remountAll();
    navigateTo(currentPage);
  });
}

// ---------------------------------------------------------------------------
// Boot.
// ---------------------------------------------------------------------------
export async function boot() {
  api = await whenDreggUi();

  appEl = document.getElementById('explorer-app');
  if (!appEl) {
    console.error('[explorer] missing <dregg-app id="explorer-app">');
    return;
  }

  setConnection('connecting');
  await buildRuntime();
  wireChrome();
  startLiveness();
  startReceiptStream();

  // Deep link: ?at=dregg://... or /explorer/<kind>/<id> path.
  const params = new URLSearchParams(window.location.search);
  const at = params.get('at');
  const routeUri = parsePathRoute(window.location.pathname);
  if (at && isRef(at)) {
    openUri(at);
  } else if (routeUri) {
    openUri(routeUri);
  } else {
    navigateTo('overview');
  }
}

// /explorer/cell/<id>, /explorer/block/<h>, /explorer/receipt/<h>, /explorer/tx/<h>
function parsePathRoute(pathname) {
  const parts = String(pathname || '').split('/').filter(Boolean);
  const idx = parts.lastIndexOf('explorer');
  if (idx === -1) return null;
  const rest = parts.slice(idx + 1).map(p => { try { return decodeURIComponent(p); } catch { return p; } });
  if (rest.length < 2) return null;
  const [rawKind, id] = rest;
  const kind = rawKind.toLowerCase();
  if (kind === 'tx' || kind === 'turn') return `dregg://turn/${id}`;
  if (kind === 'block') return `dregg://block/0/${id}`;
  if (['cell', 'receipt', 'intent', 'federation', 'capability'].includes(kind)) {
    return `dregg://${kind}/${id}`;
  }
  return null;
}

export { runtime };
