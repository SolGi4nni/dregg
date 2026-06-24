/**
 * node-link.js — the shell's connection to ONE node (your polis).
 *
 * Two jobs, kept thin (cells/inspector data flow through the shared
 * runtime-remote.js; this module owns only what the frame itself needs):
 *
 *   1. status — probe `${base}/status`, expose { ok, height, error }.
 *   2. the receipt stream — `GET /api/events/stream` (SSE, named event
 *      "receipt", id = chain index, Last-Event-ID resume). When the stream
 *      cannot be opened, fall back to polling `GET /api/events` on a
 *      since_height cursor. The mode ('sse' | 'poll' | 'off') is surfaced so
 *      the rail can say which one it is — never a fabricated "live".
 *
 * Pure DOM-free; callers subscribe with onChange/onEvent callbacks.
 */

const POLL_MS = 5000;
const MAX_EVENTS = 40;

export function createNodeLink(baseUrl) {
  const base = String(baseUrl || '').replace(/\/+$/, '');
  const listeners = { change: new Set(), event: new Set() };
  const state = {
    base,
    ok: false,
    height: 0,
    error: null,
    streamMode: 'off', // 'sse' | 'poll' | 'off'
    events: [],        // newest first, normalized
  };

  let es = null;
  let pollTimer = null;
  let sinceHeight = 0;
  let stopped = false;

  function emitChange() {
    for (const fn of listeners.change) { try { fn(state); } catch {} }
  }
  function emitEvent(ev) {
    for (const fn of listeners.event) { try { fn(ev, state); } catch {} }
  }

  async function getJSON(path) {
    const res = await fetch(`${base}${path}`, { headers: { Accept: 'application/json' } });
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    return res.json();
  }

  /** Normalize either an SSE ReceiptEvent or a polled CommittedEvent. */
  function normalizeEvent(raw, source) {
    if (!raw || typeof raw !== 'object') return null;
    const turnHash = raw.turn_hash || raw.receipt_hash || '';
    if (!turnHash) return null;
    return {
      key: `${raw.chain_index ?? ''}:${turnHash}`,
      turnHash,
      receiptHash: raw.receipt_hash || null,
      cells: Array.isArray(raw.cells) ? raw.cells : (raw.cell_id ? [raw.cell_id] : []),
      kinds: Array.isArray(raw.kinds) ? raw.kinds
        : Array.isArray(raw.effects) ? raw.effects : [],
      height: Number(raw.height || 0),
      hasProof: raw.has_proof === true || raw.proof_status === 'proved',
      finality: raw.finality || raw.status || '',
      timestamp: Number(raw.timestamp || 0),
      source, // 'sse' | 'poll'
    };
  }

  function pushEvents(rawList, source) {
    let added = 0;
    for (const raw of rawList) {
      const ev = normalizeEvent(raw, source);
      if (!ev) continue;
      if (state.events.some((e) => e.turnHash === ev.turnHash && e.height === ev.height)) continue;
      state.events.unshift(ev);
      added += 1;
      if (ev.height > sinceHeight) sinceHeight = ev.height;
      emitEvent(ev);
    }
    if (added) {
      state.events.splice(MAX_EVENTS);
      emitChange();
    }
  }

  async function probe() {
    try {
      const status = await getJSON('/status');
      state.ok = true;
      state.error = null;
      state.height = Number(
        status.height ?? status.block_height ?? status.current_height ?? status.chain_height ?? 0,
      );
    } catch (e) {
      state.ok = false;
      state.error = String(e?.message || e);
    }
    emitChange();
    return state;
  }

  async function pollOnce() {
    try {
      const data = await getJSON(`/api/events?since_height=${sinceHeight}&limit=50`);
      const list = Array.isArray(data) ? data : data.events || [];
      // Endpoint returns oldest-first after the cursor; normalize to push order.
      pushEvents(list, 'poll');
      if (state.streamMode !== 'poll') { state.streamMode = 'poll'; emitChange(); }
    } catch {
      if (state.streamMode !== 'off') { state.streamMode = 'off'; emitChange(); }
    }
  }

  function startPolling() {
    if (pollTimer || stopped) return;
    pollOnce();
    pollTimer = setInterval(pollOnce, POLL_MS);
  }

  function startStream() {
    if (stopped || typeof EventSource === 'undefined') { startPolling(); return; }
    let opened = false;
    try {
      es = new EventSource(`${base}/api/events/stream`);
    } catch {
      startPolling();
      return;
    }
    es.addEventListener('open', () => {
      opened = true;
      state.streamMode = 'sse';
      // SSE tails from the head; backfill recent history once via the poll path.
      pollOnce().then(() => { state.streamMode = 'sse'; emitChange(); });
      emitChange();
    });
    es.addEventListener('receipt', (msg) => {
      try { pushEvents([JSON.parse(msg.data)], 'sse'); } catch {}
    });
    es.addEventListener('error', () => {
      // Endpoint absent / proxy refused: fall back for the session. A drop on
      // an established stream lets EventSource auto-reconnect (and the poll
      // fallback is harmless to run alongside until it does).
      if (!opened) {
        try { es.close(); } catch {}
        es = null;
        startPolling();
      }
    });
  }

  function start() {
    probe();
    startStream();
  }

  function stop() {
    stopped = true;
    if (es) { try { es.close(); } catch {} es = null; }
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
  }

  return {
    get state() { return state; },
    base,
    start,
    stop,
    probe,
    onChange(fn) { listeners.change.add(fn); return () => listeners.change.delete(fn); },
    onEvent(fn) { listeners.event.add(fn); return () => listeners.event.delete(fn); },
  };
}

const NODE_KEY = 'dregg.remote.baseUrl';
export const DEFAULT_NODE = 'https://devnet.dregg.fg-goose.online';

/** Node URL resolution: ?node= param > saved choice > same-origin node > devnet. */
export function resolveNodeUrl() {
  try {
    const param = new URLSearchParams(window.location.search).get('node');
    if (param) return param.replace(/\/+$/, '');
  } catch {}
  try {
    const saved = localStorage.getItem(NODE_KEY);
    if (saved) return saved.replace(/\/+$/, '');
  } catch {}
  return DEFAULT_NODE;
}

export function saveNodeUrl(url) {
  try { localStorage.setItem(NODE_KEY, String(url).replace(/\/+$/, '')); } catch {}
}
