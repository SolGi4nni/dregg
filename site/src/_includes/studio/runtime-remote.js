/**
 * RemoteRuntime — read-only Runtime over a live dregg federation node's HTTP API.
 *
 * Mirrors the API shape of createInMemoryRuntime, but every mutation throws
 * NotPermitted: this runtime is a viewport, not a controller. The live node
 * decides what writes happen.
 *
 * Polling: every POLL_INTERVAL_MS we refresh /status and /api/cells. If the
 * status height or the cell list shape changes, we bump `version` (and `cursor`,
 * if height moved) so dependent signals re-render. Network failures are logged
 * once per failure and the previously-cached value is retained — we don't
 * thrash on flaky links and we don't error-storm the console.
 *
 * The endpoint conventions match explorer/api.js (status at /status, cells at
 * /api/cells, single cell at /api/cell/<id>). We intentionally don't import
 * api.js — that module is bound to localStorage-configured base URL + the
 * explorer's auth flow; this runtime takes its base URL explicitly.
 *
 * CORS realism: when used against devnet.dregg.fg-goose.online from a
 * browser-localhost origin the fetches will reject with a CORS error. The
 * runtime still constructs cleanly; signals stay null until the network
 * cooperates. (FOLLOWUP-07: now surfaces actionable guidance in logs for
 * Starbridge users; see improved logOnce + getJSON catch.)
 */

import { attachRuntimeObjectAdapter } from './runtime-object-adapter.js';

const POLL_INTERVAL_MS = 5000;

const CAPS = Object.freeze({
  read: true,
  mutate: false,
  debug: false,
  timeTravel: false,
});

function notPermitted(op) {
  return () => {
    throw new Error(`NotPermitted: RemoteRuntime is read-only (${op})`);
  };
}

export async function createRemoteRuntime({ signals, baseUrl }) {
  if (!signals || typeof signals.signal !== 'function') {
    throw new Error('createRemoteRuntime: signals.signal is required');
  }
  const { signal } = signals;
  const base = String(baseUrl || '').replace(/\/+$/, '');

  const version = signal(0);
  const cursor = signal(0);
  const events = new EventTarget();

  // Observability live events (Task #30). Same signal shape as InMemoryRuntime.
  // Populated by two sources merged together (F2):
  //   - SSE /observability/stream — live, low-latency trace events (no backlog).
  //   - polled /api/events        — committed history with typed proof_status.
  // <dregg-activity> consumes the merged feed and renders a proof_status badge.
  const traceEventsSignal = signal({ schema_version: 1, event_count: 0, events: [] });
  function getTraceEvents() { return traceEventsSignal; }

  // Latest payload from each source; republished as a merged, de-duplicated feed.
  let sseEvents = [];          // events from the SSE stream
  let committedEvents = [];    // events mapped from /api/events committed history
  let lastEventsHeight = 0;    // high-water mark for /api/events since_height cursor

  // Merge SSE (live) + committed (history) into a single chronological feed,
  // de-duplicated by a stable identity key. Committed events win on conflict
  // because they carry the authoritative proof_status. Published oldest→newest
  // so <dregg-activity> (which reverses for display) shows newest first.
  function publishMergedTraceEvents() {
    const byKey = new Map();
    for (const e of committedEvents) byKey.set(traceEventKey(e), e);
    for (const e of sseEvents) {
      const k = traceEventKey(e);
      if (!byKey.has(k)) byKey.set(k, e);
    }
    const merged = Array.from(byKey.values()).sort(compareTraceEvents);
    traceEventsSignal.value = {
      schema_version: 1,
      schema_name: 'dregg-observability-event-stream-v1',
      event_count: merged.length,
      events: merged,
    };
  }

  // SSE consumer for remote observability stream (broadcast from node).
  // Uses browser EventSource; pushes parsed JSON log into the live source.
  let obsEs = null;
  if (base && typeof EventSource !== 'undefined') {
    try {
      obsEs = new EventSource(`${base}/observability/stream`);
      obsEs.onmessage = (msg) => {
        try {
          const data = JSON.parse(msg.data || '{}');
          sseEvents = Array.isArray(data && data.events) ? data.events : [];
          publishMergedTraceEvents();
        } catch {}
      };
      obsEs.onerror = () => { /* keep last good value */ };
    } catch {}
  }

  // Poll /api/events for committed history with proof_status (F2). Unlike the
  // SSE stream (live-only), this gives a backlog the moment the page opens and
  // a typed proof_status per event. Mapped into the same TraceEvent shape so a
  // single <dregg-activity> renders both. since_height advances the cursor.
  async function pollEventsOnce() {
    if (destroyed || !base) return;
    const data = await getJSON(`/api/events?since_height=0&limit=200`);
    if (destroyed || !Array.isArray(data)) return;
    const mapped = data.map(committedEventToTraceEvent);
    // Cheap change detection: count + last height.
    const top = data.reduce((m, e) => Math.max(m, Number(e.height || 0)), 0);
    if (mapped.length !== committedEvents.length || top !== lastEventsHeight) {
      committedEvents = mapped;
      lastEventsHeight = top;
      publishMergedTraceEvents();
    }
  }

  // --- Extension bridge for passive debugger (Phase 1/2, STARBRIDGE-FOLLOWUP-06) ---
  // When running inside the Dragon's Egg Cipherclerk extension (iframe panel, or any
  // extension page), chrome.runtime is present. We poll the background's
  // synthesized activity feed (populated from the live WS bus + cclerk ops,
  // exactly the TraceEvent shape for <dregg-activity>) via "dregg:getActivityFeed".
  // This lets RemoteRuntime (and all inspectors including activity) work against
  // *real node events* using the extension's authenticated connection, without
  // needing direct node /observability/stream (avoids CORS/auth issues).
  // High-leverage integration: makes the embedded debugger vision real even before
  // full studio assets are packaged into the extension.
  let extPollTimer = null;
  const isExtensionContext = (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.sendMessage);
  if (isExtensionContext) {
    const pollExtFeed = async () => {
      if (destroyed) return;
      try {
        const resp = await new Promise((resolve) => {
          chrome.runtime.sendMessage({ type: 'dregg:getActivityFeed' }, (r) => resolve(r));
        });
        if (resp && resp.result) {
          traceEventsSignal.value = resp.result;
        }
      } catch (e) { /* keep last; background may not be ready */ }
    };
    pollExtFeed();
    extPollTimer = setInterval(pollExtFeed, 2000);  // live enough for debugger feed
  }

  // Cached payloads. Signals are read on demand by callers; we hold the latest
  // successful value here and surface it via per-id signal wrappers.
  let cachedStatus = null;            // last /status response
  let cachedCellList = null;          // last /api/cells response
  let cachedReceipts = null;          // last receipt API response
  let cachedBlocks = null;            // last block/root API response
  let cachedFederations = null;       // explicit or synthesized federation list
  let cachedIntents = null;           // last /api/intents response
  let cachedTokens = null;            // last /api/tokens response (capabilities)
  const cellSignals = new Map();      // id -> signal<CellState | null>
  const cellPending = new Map();      // id -> in-flight Promise (dedupe)
  let listSignal = null;              // signal<CellSummary[] | null>
  let receiptListSignal = null;
  let blockListSignal = null;
  let federationListSignal = null;
  let intentListSignal = null;
  let capabilityListSignal = null;
  const receiptSignals = new Map();
  const receiptWitnessPending = new Map(); // hash -> in-flight Promise (dedupe lazy witness fetch)
  const receiptWitnessFetched = new Set(); // hash -> already merged DWR1 artifacts (don't refetch)
  const blockSignals = new Map();
  const intentSignals = new Map();

  // One AbortController per runtime instance; aborted on destroy(). Every
  // fetch wires this in so destroy() actually cancels in-flight requests.
  const abort = new AbortController();
  let pollTimer = null;
  let destroyed = false;

  // Log each distinct error once per kind to avoid console spam.
  const loggedErrors = new Set();
  function logOnce(key, err) {
    if (loggedErrors.has(key)) return;
    loggedErrors.add(key);
    // eslint-disable-next-line no-console
    console.warn(`[RemoteRuntime] ${key}:`, err && err.message ? err.message : err);
  }

  function isCorsError(err) {
    if (!err) return false;
    const m = (err.message || err.toString() || '').toLowerCase();
    return m.includes('cors') || m.includes('failed to fetch') || (err.name === 'TypeError' && m.includes('fetch'));
  }

  async function getJSON(path) {
    if (destroyed) return null;
    if (!base) return null;
    try {
      const res = await fetch(`${base}${path}`, {
        headers: { Accept: 'application/json' },
        signal: abort.signal,
      });
      if (!res.ok) {
        logOnce(`GET ${path} ${res.status}`, new Error(`status ${res.status}`));
        return null;
      }
      return await res.json();
    } catch (err) {
      // AbortError on destroy is expected; swallow silently.
      if (err && err.name === 'AbortError') return null;
      if (isCorsError(err)) {
        // High-signal for Starbridge users (the primary RemoteRuntime consumers).
        logOnce(`GET ${path} CORS_BLOCKED`, new Error(
          `CORS blocked contacting ${base}. Starbridge Remote against non-local nodes requires the node to allow browser origins (node/src/api.rs cors_middleware currently localhost+extension only; discord-bot is permissive). Workarounds: (1) use the Chrome extension's embedded Starbridge panel, (2) run a local node with relaxed CORS for dev, (3) target the discord-bot HTTP surface. Original err: ${err.message || err}`
        ));
      } else {
        logOnce(`GET ${path} failed`, err);
      }
      return null;
    }
  }

  async function getFirstJSON(paths) {
    for (const path of paths) {
      const data = await getJSON(path);
      if (data != null) return data;
    }
    return null;
  }

  function fire(type, detail) {
    events.dispatchEvent(new CustomEvent(type, { detail }));
  }
  function bump() { version.value = version.value + 1; }

  // --- Polling ----------------------------------------------------------
  async function pollOnce() {
    if (destroyed) return;
    const [status, cells, receipts, blocks, federations, intents, tokens] = await Promise.all([
      getJSON('/status'),
      getJSON('/api/cells'),
      getFirstJSON(['/api/starbridge/receipts?limit=100', '/api/receipts', '/api/receipts/recent']),
      // Prefer the real blocklace DAG (lane: node consensus) — height-sorted
      // BlockView with real prev_hash/predecessors. Fall back to the legacy
      // attested-roots alias for older nodes that lack the DAG route.
      getFirstJSON(['/api/blocklace/blocks', '/api/blocks', '/federation/roots']),
      getFirstJSON(['/api/federations']),
      getJSON('/api/intents'),
      getJSON('/api/tokens'),
    ]);
    if (destroyed) return;

    let changed = false;

    if (status) {
      // Height field is best-effort — different node versions name it
      // differently; try a few. cursor stays at 0 if none are present.
      const h = pickHeight(status);
      if (typeof h === 'number' && h !== cursor.value) {
        cursor.value = h;
        changed = true;
      }
      if (!shallowEqual(status, cachedStatus)) {
        cachedStatus = status;
        changed = true;
      }
    }

    if (cells) {
      // Cheap change detection: compare length + last-id. Good enough to
      // know whether to re-fetch derived signals.
      const normalized = normalizeCells(cells);
      const sigChanged = !sameCellListShape(normalized, cachedCellList);
      cachedCellList = normalized;
      if (listSignal) listSignal.value = normalized;
      if (sigChanged) changed = true;
    }

    if (receipts) {
      const normalized = normalizeReceipts(receipts);
      if (!sameIdListShape(normalized, cachedReceipts, receiptIdOf)) changed = true;
      cachedReceipts = normalized;
      if (receiptListSignal) receiptListSignal.value = normalized;
      // Re-point observed single-receipt signals at the freshly polled record,
      // but carry forward any DWR1 witness artifacts already lazy-fetched for
      // that hash so a poll doesn't wipe the merged blobs (F1).
      for (const [id, sig] of receiptSignals) {
        sig.value = withMergedWitnesses(findReceipt(normalized, id), sig.value);
      }
    }

    if (blocks) {
      const normalized = normalizeBlocks(blocks);
      if (!sameIdListShape(normalized, cachedBlocks, blockIdOf)) changed = true;
      cachedBlocks = normalized;
      if (blockListSignal) blockListSignal.value = normalized;
      for (const [key, sig] of blockSignals) sig.value = findBlock(normalized, key);
    }

    if (intents) {
      const normalized = normalizeIntents(intents);
      if (!sameIdListShape(normalized, cachedIntents, intentIdOf)) changed = true;
      cachedIntents = normalized;
      if (intentListSignal) intentListSignal.value = normalized;
      for (const [id, sig] of intentSignals) sig.value = findIntent(normalized, id);
    }

    if (tokens) {
      const normalized = normalizeTokens(tokens);
      if (!sameIdListShape(normalized, cachedTokens, tokenIdOf)) changed = true;
      cachedTokens = normalized;
      if (capabilityListSignal) capabilityListSignal.value = normalized;
    }

    const normalizedFederations = normalizeFederations(federations, status, cachedBlocks);
    if (!sameIdListShape(normalizedFederations, cachedFederations, federationIdOf)) changed = true;
    cachedFederations = normalizedFederations;
    if (federationListSignal) federationListSignal.value = normalizedFederations;

    if (changed) {
      bump();
      fire('poll', { status: cachedStatus, cells: cachedCellList });
    }

    // Refresh the committed activity backlog (F2). Independent of `changed` so
    // newly-proven events surface even when cell/receipt shapes are stable.
    await pollEventsOnce();
  }

  function startPolling() {
    // Fire immediately so first-read isn't blocked for 5s; then on interval.
    pollOnce();
    pollTimer = setInterval(pollOnce, POLL_INTERVAL_MS);
  }

  // --- Public getters ---------------------------------------------------
  function listCells() {
    if (!listSignal) listSignal = signal(cachedCellList);
    return listSignal;
  }

  function getCell(id) {
    if (!cellSignals.has(id)) {
      const sig = signal(null);
      cellSignals.set(id, sig);
      // Kick off a fetch; result populates the signal asynchronously.
      // Subsequent calls return the same signal and re-fetch is triggered
      // by version bumps (see refreshCells below).
      fetchCellInto(id, sig);
    }
    return cellSignals.get(id);
  }

  async function fetchCellInto(id, sig) {
    if (cellPending.has(id)) return cellPending.get(id);
    const p = (async () => {
      const data = await getJSON(`/api/cell/${encodeURIComponent(id)}`);
      if (destroyed) return;
      sig.value = normalizeCell(data, id);
    })();
    cellPending.set(id, p);
    try { await p; } finally { cellPending.delete(id); }
  }

  // Refresh any observed individual cell signals whenever version changes.
  // We don't have a real subscribe loop for those — piggy-back on the poll.
  events.addEventListener('poll', () => {
    for (const [id, sig] of cellSignals) fetchCellInto(id, sig);
    // Retry lazy witness fetch for observed receipts that weren't proven yet
    // (artifacts may appear once the node finishes proving the turn).
    for (const [id, sig] of receiptSignals) {
      const hash = String(id || '').toLowerCase();
      if (!receiptWitnessFetched.has(hash)) fetchReceiptWitnessesInto(id, sig);
    }
  });

  function listReceipts() {
    if (!receiptListSignal) receiptListSignal = signal(cachedReceipts || []);
    return receiptListSignal;
  }

  // Per-cell receipt history (the time-travel surface). The node filters
  // server-side via /api/starbridge/receipts?cell=<id> (matches agent +
  // touched cells); we keep one signal per cell, refreshed on every poll so
  // the timeline stays live. Falls back to nothing (empty signal) when the
  // starbridge route is absent — the inspector then filters listReceipts().
  const cellReceiptSignals = new Map();
  function listCellReceipts(cellId) {
    const id = String(cellId || '').toLowerCase();
    if (!cellReceiptSignals.has(id)) {
      const sig = signal(null); // null = not-yet-fetched (distinguish from [])
      cellReceiptSignals.set(id, sig);
      const refresh = async () => {
        const data = await getJSON(`/api/starbridge/receipts?cell=${encodeURIComponent(id)}&limit=200`);
        if (destroyed) return;
        if (data) sig.value = normalizeReceipts(data);
        else if (sig.value === null) sig.value = [];
      };
      refresh();
      events.addEventListener('poll', refresh);
    }
    return cellReceiptSignals.get(id);
  }

  function getReceipt(id) {
    if (!receiptSignals.has(id)) {
      receiptSignals.set(id, signal(findReceipt(cachedReceipts, id)));
    }
    const sig = receiptSignals.get(id);
    // F1: the receipt-list payload never carries DWR1 witness blobs. Lazy-fetch
    // GET /api/receipts/{hash}/witnesses on first observation and merge the real
    // artifact_format + witness_artifacts + witnessed_receipts into the signal,
    // so <dregg-witnessed-receipt> can render scope-2 artifacts instead of
    // always falling back to "not exposed".
    fetchReceiptWitnessesInto(id, sig);
    return sig;
  }

  // Lazy single-fetch of the per-receipt DWR1 witness artifacts. Resolves the
  // receipt hash (a turn/receipt hash is the path key), merges the response
  // fields into the receipt signal, and dedupes via receiptWitnessPending.
  async function fetchReceiptWitnessesInto(id, sig) {
    const hash = String(id || '').toLowerCase();
    if (!/^[0-9a-f]{64}$/.test(hash)) return; // witness route keys on a 32-byte hash
    if (receiptWitnessFetched.has(hash) || receiptWitnessPending.has(hash)) return;
    const p = (async () => {
      const data = await getJSON(`/api/receipts/${hash}/witnesses`);
      if (destroyed || !data) return;
      const artifacts = Array.isArray(data.witness_artifacts) ? data.witness_artifacts : [];
      // Only mark "fetched" (and merge) when the node actually returns artifacts;
      // an empty list for a not-yet-proven receipt should be retried after the
      // next poll bump rather than cached as "no witnesses, ever".
      if (!artifacts.length) return;
      receiptWitnessFetched.add(hash);
      const witnessFields = {
        artifact_format: data.artifact_format || 'DWR1',
        witness_artifacts: artifacts,
        witness_count: Number(data.witness_count ?? artifacts.length),
        has_witness: true,
        witnessed_receipts: Array.isArray(data.witnessed_receipts) ? data.witnessed_receipts : undefined,
      };
      // Merge onto whatever the signal currently holds (poll may have refreshed
      // it). If the base receipt hasn't loaded yet, seed a minimal record so the
      // artifacts aren't lost.
      const base = sig.value || findReceipt(cachedReceipts, id) || { turn_hash: hash, receipt_hash: hash };
      sig.value = { ...base, ...witnessFields };
    })();
    receiptWitnessPending.set(hash, p);
    try { await p; } finally { receiptWitnessPending.delete(hash); }
  }

  function listBlocks() {
    if (!blockListSignal) blockListSignal = signal(cachedBlocks || []);
    return blockListSignal;
  }

  function getBlock(ref) {
    const key = typeof ref === 'object'
      ? `${ref.fedIndex ?? ref.fed_index ?? 0}/${ref.height ?? ref.block_height ?? 0}`
      : `0/${ref}`;
    if (!blockSignals.has(key)) blockSignals.set(key, signal(findBlock(cachedBlocks, key)));
    return blockSignals.get(key);
  }

  // A turn and its receipt share the same hash in the node's read surface; the
  // <dregg-turn> inspector consumes the same receipt shape, so getTurn aliases
  // getReceipt (matches InMemoryRuntime, which does the same).
  function getTurn(id) { return getReceipt(id); }

  function listIntents() {
    if (!intentListSignal) intentListSignal = signal(cachedIntents || []);
    return intentListSignal;
  }

  function getIntent(idOrIndex) {
    const key = String(idOrIndex);
    if (!intentSignals.has(key)) {
      intentSignals.set(key, signal(findIntent(cachedIntents, idOrIndex)));
    }
    return intentSignals.get(key);
  }

  // Capabilities/tokens. The node exposes the node cipherclerk's own held tokens
  // at /api/tokens (a flat list), not per-agent capability trees. We surface the
  // flat list for <dregg-capability-list> and resolve single tokens by id/slot.
  function listCapabilities(_agentIdx) {
    if (!capabilityListSignal) capabilityListSignal = signal(cachedTokens || []);
    return capabilityListSignal;
  }

  function getCapability(idOrAgent, slotOrIndex) {
    const sig = signal(null);
    const update = () => {
      const list = cachedTokens || [];
      const wantId = String(idOrAgent ?? '');
      const wantSlot = slotOrIndex != null ? String(slotOrIndex) : null;
      sig.value = list.find((t) =>
        String(t.id ?? '') === wantId ||
        (wantSlot != null && String(t.slot ?? '') === wantSlot) ||
        (wantSlot != null && String(t.id ?? '') === wantSlot)
      ) || (wantSlot != null ? list[Number(wantSlot)] : null) || null;
    };
    update();
    events.addEventListener('poll', update);
    return sig;
  }

  // Outbox is an extension/sim-only concept (pending local submissions). A
  // read-only remote viewport has none; return an always-empty signal so the
  // shared <dregg-outbox> inspector renders its honest empty state.
  let outboxSignal = null;
  function getOutbox() {
    if (!outboxSignal) outboxSignal = signal([]);
    return outboxSignal;
  }

  function listKnownFederations() {
    if (!federationListSignal) federationListSignal = signal(cachedFederations || []);
    return federationListSignal;
  }

  function getFederation(idOrIndex) {
    const sig = signal(null);
    const update = () => {
      const want = String(idOrIndex ?? '0');
      sig.value = (cachedFederations || []).find((f) =>
        String(f.fed_index ?? '') === want ||
        String(f.id ?? '') === want ||
        String(f.federation_id ?? '') === want ||
        String(f.name ?? '') === want
      ) || null;
    };
    update();
    events.addEventListener('poll', update);
    return sig;
  }

  function destroy() {
    if (destroyed) return;
    destroyed = true;
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
    if (extPollTimer) { clearInterval(extPollTimer); extPollTimer = null; }
    if (obsEs) { try { obsEs.close(); } catch {} obsEs = null; }
    try { abort.abort(); } catch { /* noop */ }
  }

  startPolling();

  return attachRuntimeObjectAdapter({
    caps: CAPS,
    source: { kind: 'remote', label: `remote ${base || '(unset)'}` },
    version,
    cursor,
    events,

    // The node's HTTP base + a read helper, so the ORGAN inspectors
    // (trustline / channels / mailbox / court) can read their LIVE status
    // routes (/trustline/status/* /channels/status/* /relay/inbox/* /court/status/*)
    // — those organs are node-side services with no per-cell signal here.
    // Returns null on any failure (CORS / absent route / offline) so the
    // inspector renders an honest "unreachable", never a fabricated state.
    nodeBase: base || null,
    nodeGet: (path) => getJSON(path),

    getCell,
    listCells,
    listReceipts,
    listCellReceipts,
    getReceipt,
    getTurn,
    listIntents,
    getIntent,
    listCapabilities,
    getCapability,
    getOutbox,
    listKnownFederations,
    getFederation,
    listBlocks,
    getBlock,
    getTraceEvents,

    // Read-only: all mutations refuse.
    createAgent: notPermitted('createAgent'),
    createCell: notPermitted('createCell'),
    executeTurn: notPermitted('executeTurn'),
    mintToken: notPermitted('mintToken'),
    advanceHeight: notPermitted('advanceHeight'),

    destroy,
  });
}

// --- helpers ------------------------------------------------------------

function pickHeight(status) {
  if (!status || typeof status !== 'object') return null;
  // Common field names seen across node versions.
  const candidates = ['latest_height', 'height', 'block_height', 'tip_height', 'head_height', 'cursor'];
  for (const k of candidates) {
    const v = status[k];
    if (typeof v === 'number') return v;
    if (typeof v === 'string' && /^\d+$/.test(v)) return Number(v);
  }
  return null;
}

function sameCellListShape(a, b) {
  if (a === b) return true;
  if (!Array.isArray(a) || !Array.isArray(b)) return false;
  if (a.length !== b.length) return false;
  // Compare ids at head + tail; cheap and adequate for change detection.
  const idOf = (x) => x && (x.id || x.cell_id || x.hash);
  return idOf(a[0]) === idOf(b[0]) && idOf(a[a.length - 1]) === idOf(b[b.length - 1]);
}

function sameIdListShape(a, b, idOf) {
  if (a === b) return true;
  if (!Array.isArray(a) || !Array.isArray(b)) return false;
  if (a.length !== b.length) return false;
  return idOf(a[0]) === idOf(b[0]) && idOf(a[a.length - 1]) === idOf(b[b.length - 1]);
}

function normalizeCells(cells) {
  return Array.isArray(cells) ? cells.map((cell) => normalizeCell(cell)).filter(Boolean) : [];
}

function normalizeCell(cell, fallbackId = '') {
  if (!cell || typeof cell !== 'object') return null;
  const id = cell.cell_id || cell.id || fallbackId;
  return {
    ...cell,
    id,
    cell_id: id,
    balance: cell.balance ?? cell.state?.balance ?? 0,
    nonce: cell.nonce ?? cell.state?.nonce ?? 0,
    num_capabilities: cell.num_capabilities ?? cell.capability_count ?? cell.capabilities?.length ?? 0,
    proved_state: cell.proved_state ?? cell.provedState ?? false,
    delegation_epoch: cell.delegation_epoch ?? cell.delegationEpoch ?? 0,
    program: cell.program || (cell.program_kind ? { kind: cell.program_kind } : null),
  };
}

function normalizeReceipts(receipts) {
  const list = Array.isArray(receipts) ? receipts : (Array.isArray(receipts?.receipts) ? receipts.receipts : []);
  return list.map((entry) => {
    const r = entry.receipt || entry;
    const turnHash = r.turn_hash || r.turnHash || r.hash || r.receipt_hash || '';
    // NOTE: the receipt-LIST payload (node `ReceiptInfo`) carries `has_witness`
    // + `witness_count` but NOT the DWR1 hex blobs — those live only at
    // GET /api/receipts/{hash}/witnesses and are merged in lazily by
    // fetchReceiptWitnessesInto() on first getReceipt(). So we DON'T fabricate
    // `artifact_format`/`witness_artifacts` here: they stay absent until the
    // node confirms them, and <dregg-witnessed-receipt> renders real artifacts.
    const witnessCount = Number(r.witness_count ?? 0);
    return {
      ...entry,
      ...r,
      turn_hash: turnHash,
      receipt_hash: r.receipt_hash || r.receiptHash || turnHash,
      pre_state_hash: r.pre_state_hash || r.pre_state || r.preState || '',
      post_state_hash: r.post_state_hash || r.post_state || r.postState || '',
      action_count: r.action_count ?? r.actions?.length ?? 0,
      computrons_used: r.computrons_used ?? r.computrons ?? 0,
      timestamp: r.timestamp ?? r.committed_at ?? '',
      has_witness: Boolean(r.has_witness || witnessCount > 0),
      witness_count: witnessCount,
      proof_view: r.proof_view || (r.has_proof || r.has_witness || witnessCount > 0 ? {
        kind: (r.has_witness || witnessCount > 0) ? 'WitnessedReceipt' : 'ExecutorSignature',
        public_inputs: [],
        bilateral_pi: null,
        is_agent_cell: false,
        is_sovereign_cell: false,
      } : null),
    };
  }).filter((r) => r.turn_hash || r.receipt_hash);
}

function receiptIdOf(r) {
  return r && (r.turn_hash || r.receipt_hash || r.hash);
}

function findReceipt(receipts, id) {
  const want = String(id || '').toLowerCase();
  return (receipts || []).find((r) =>
    String(r.turn_hash || '').toLowerCase() === want ||
    String(r.receipt_hash || '').toLowerCase() === want ||
    String(r.hash || '').toLowerCase() === want
  ) || null;
}

// Carry forward DWR1 witness artifacts already lazy-fetched onto `prev` when a
// poll produces a fresh `next` record for the same receipt (F1). The list
// payload never has these fields, so a naive overwrite would drop them.
function withMergedWitnesses(next, prev) {
  if (!next) return next;
  if (!prev || !Array.isArray(prev.witness_artifacts) || prev.witness_artifacts.length === 0) {
    return next;
  }
  return {
    ...next,
    artifact_format: prev.artifact_format || 'DWR1',
    witness_artifacts: prev.witness_artifacts,
    witness_count: prev.witness_count ?? next.witness_count,
    has_witness: true,
    witnessed_receipts: prev.witnessed_receipts ?? next.witnessed_receipts,
  };
}

// Map a node CommittedEvent ({height, status, proof_status, turn_hash,
// cell_id, effects, timestamp}) into the TraceEvent shape <dregg-activity>
// renders. We use the `turn_lifecycle` kind (the only committed-turn variant)
// and carry status + proof_status on the payload so the inspector can badge it.
function committedEventToTraceEvent(e) {
  const effects = Array.isArray(e.effects) ? e.effects : [];
  const phase = e.status === 'rejected' ? 'rejected' : 'committed';
  return {
    kind: 'turn_lifecycle',
    source: 'committed',
    envelope: {
      seq: Number(e.height || 0),
      timestamp: secondsToIso(e.timestamp),
      actor: e.cell_id || '',
      height: Number(e.height || 0),
    },
    payload: {
      phase,
      proof_status: e.proof_status || null,
      status: e.status || null,
      receipt_hash: e.turn_hash || '',
      turn_hash: e.turn_hash || '',
      cell_id: e.cell_id || '',
      effects,
      action_count: effects.length,
      reason: phase === 'rejected' ? (effects.join(', ') || 'rejected') : undefined,
    },
  };
}

function secondsToIso(ts) {
  const n = Number(ts);
  if (!Number.isFinite(n) || n <= 0) return '';
  // CommittedEvent.timestamp is unix seconds.
  const ms = n > 10_000_000_000 ? n : n * 1000;
  const d = new Date(ms);
  return Number.isNaN(d.getTime()) ? '' : d.toISOString();
}

// Stable identity for a trace event so SSE-live and committed-history copies of
// the same turn collapse to one row. Falls back to a JSON digest when no hash.
function traceEventKey(e) {
  const env = e.envelope || {};
  const pl = e.payload || {};
  const hash = pl.turn_hash || pl.receipt_hash || '';
  if (hash) return `${e.kind || '?'}:${hash}:${pl.phase || ''}`;
  return `${e.kind || '?'}:${env.seq ?? ''}:${env.timestamp ?? ''}`;
}

// Order trace events oldest→newest by height/seq then timestamp.
function compareTraceEvents(a, b) {
  const ea = a.envelope || {}, eb = b.envelope || {};
  const ha = Number(ea.height ?? ea.seq ?? 0), hb = Number(eb.height ?? eb.seq ?? 0);
  if (ha !== hb) return ha - hb;
  return String(ea.timestamp || '').localeCompare(String(eb.timestamp || ''));
}

function normalizeBlocks(blocks) {
  const list = Array.isArray(blocks) ? blocks : (Array.isArray(blocks?.blocks) ? blocks.blocks : []);
  return list.map((block) => {
    const height = block.height ?? block.block_height ?? block.index ?? 0;
    const fedIndex = block.fed_index ?? block.federation_index ?? 0;
    const hash = block.block_hash || block.hash || block.merkle_root || block.root || '';
    return {
      ...block,
      height,
      block_height: height,
      fed_index: fedIndex,
      block_hash: hash,
      events: Array.isArray(block.events) ? block.events : (block.merkle_root ? [`root:${block.merkle_root}`] : []),
    };
  });
}

function blockIdOf(b) {
  return b ? `${b.fed_index ?? 0}/${b.height ?? b.block_height ?? 0}/${b.block_hash || ''}` : '';
}

function findBlock(blocks, key) {
  const [fed, height] = String(key || '').split('/');
  return (blocks || []).find((b) =>
    String(b.fed_index ?? 0) === String(fed ?? 0) &&
    String(b.height ?? b.block_height ?? 0) === String(height ?? '')
  ) || null;
}

function normalizeFederations(federations, status, blocks) {
  const explicit = Array.isArray(federations) ? federations : (Array.isArray(federations?.federations) ? federations.federations : []);
  if (explicit.length) return explicit.map((f, idx) => normalizeFederation(f, idx, blocks));
  if (!status) return [];
  return [normalizeFederation(status, 0, blocks)];
}

function normalizeFederation(f, idx, blocks) {
  const height = pickHeight(f) ?? (blocks || []).reduce((max, b) => Math.max(max, Number(b.height || 0)), 0);
  return {
    ...f,
    fed_index: f.fed_index ?? f.registered_index ?? idx,
    name: f.name || f.federation_name || f.federation_id || f.silo_id || 'remote federation',
    height,
    num_nodes: f.num_nodes ?? f.member_count ?? f.nodes ?? f.federation_members ?? f.peer_count ?? 0,
    num_events: f.num_events ?? f.events ?? 0,
    num_finalized_roots: f.num_finalized_roots ?? (blocks || []).length,
    latest_root: f.latest_root || f.merkle_root || f.root || (blocks || [])[blocks.length - 1]?.block_hash || null,
  };
}

function federationIdOf(f) {
  return f && (f.fed_index ?? f.id ?? f.federation_id ?? f.name);
}

function normalizeIntents(intents) {
  // Node /api/intents returns Vec<{ id, intent }>; tolerate a bare-array form.
  const list = Array.isArray(intents)
    ? intents
    : (Array.isArray(intents?.intents) ? intents.intents : []);
  return list.map((entry, idx) => {
    const inner = entry && typeof entry === 'object' && entry.intent ? entry.intent : entry;
    const id = entry?.id || entry?.intent_id || inner?.id || inner?.intent_id || String(idx);
    return {
      ...(inner || {}),
      ...entry,
      intent_id: id,
      id,
      intent_index: idx,
      kind: inner?.kind || inner?.type || entry?.kind || 'intent',
    };
  });
}

function intentIdOf(i) {
  return i && (i.intent_id || i.id);
}

function findIntent(intents, idOrIndex) {
  const list = intents || [];
  const asNum = Number(idOrIndex);
  if (!Number.isNaN(asNum) && list[asNum]) return list[asNum];
  const want = String(idOrIndex || '');
  return list.find((i) => String(i.intent_id || i.id || '') === want) || null;
}

function normalizeTokens(tokens) {
  const list = Array.isArray(tokens)
    ? tokens
    : (Array.isArray(tokens?.tokens) ? tokens.tokens : []);
  return list.map((t, idx) => ({
    ...t,
    id: t.id || t.token_id || String(idx),
    label: t.label || t.id || `token ${idx}`,
    service: t.service || '',
    slot: t.slot ?? idx,
  }));
}

function tokenIdOf(t) {
  return t && (t.id || t.token_id || t.label);
}

function shallowEqual(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  const ka = Object.keys(a), kb = Object.keys(b);
  if (ka.length !== kb.length) return false;
  for (const k of ka) if (a[k] !== b[k]) return false;
  return true;
}
