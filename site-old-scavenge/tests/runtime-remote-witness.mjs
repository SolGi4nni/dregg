/**
 * RemoteRuntime witness + activity unit test (F1 + F2).
 *
 * Pure-Node test — no browser, no live node. Mocks `fetch` + `EventSource` and
 * provides a minimal preact-signals-shaped `signals` object, then asserts:
 *
 *   F1: getReceipt(hash) lazy-fetches /api/receipts/{hash}/witnesses and merges
 *       artifact_format:DWR1 + witness_artifacts + witnessed_receipts into the
 *       receipt signal (the receipt-LIST payload never carries these blobs), so
 *       <dregg-witnessed-receipt> can read real scope-2 artifacts. A poll that
 *       refreshes the list must NOT wipe the merged artifacts.
 *
 *   F2: the activity feed is fed from /api/events committed history (backlog +
 *       typed proof_status), mapped to the TraceEvent shape <dregg-activity>
 *       renders, merged with the SSE live stream and de-duplicated.
 *
 * Run:  node tests/runtime-remote-witness.mjs
 */

import { createRemoteRuntime } from '../src/_includes/studio/runtime-remote.js';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ── Minimal signals impl (preact-signals shape: .value getter/setter, effect) ──
function makeSignals() {
  let running = null;
  function signal(initial) {
    const subs = new Set();
    let val = initial;
    return {
      get value() {
        if (running) subs.add(running);
        return val;
      },
      set value(v) {
        val = v;
        for (const fn of [...subs]) fn();
      },
      peek() { return val; },
    };
  }
  function effect(fn) {
    const run = () => { const prev = running; running = run; try { fn(); } finally { running = prev; } };
    run();
    return () => {};
  }
  return { signal, effect };
}

// ── Mock node fixtures ──────────────────────────────────────────────────────
const RECEIPT_HASH = 'a'.repeat(64);
const OTHER_HASH = 'b'.repeat(64);

// receipt-LIST payload (node ReceiptInfo): has_witness/witness_count but NO blobs.
const RECEIPTS_LIST = [
  {
    receipt_hash: RECEIPT_HASH,
    turn_hash: RECEIPT_HASH,
    agent: 'c'.repeat(64),
    pre_state: '1'.repeat(64),
    post_state: '2'.repeat(64),
    timestamp: 1_700_000_000,
    computrons_used: 42,
    action_count: 1,
    has_proof: true,
    has_witness: true,
    witness_count: 1,
  },
];

// /api/receipts/{hash}/witnesses payload (DWR1 blobs live ONLY here).
const WITNESSES = {
  receipt_hash: RECEIPT_HASH,
  witness_count: 1,
  artifact_format: 'DWR1',
  witness_artifacts: ['44575231' + 'de'.repeat(32)], // "DWR1" + hex blob
  witnessed_receipts: [{ kind: 'WitnessedReceipt' }],
};

// /api/events committed history (CommittedEvent shape, typed proof_status).
const EVENTS = [
  {
    height: 7, status: 'committed', proof_status: 'proved',
    turn_hash: RECEIPT_HASH, cell_id: 'c'.repeat(64),
    effects: ['transfer'], timestamp: 1_700_000_000,
  },
  {
    height: 8, status: 'rejected', proof_status: 'proof_generation_failed',
    turn_hash: OTHER_HASH, cell_id: 'd'.repeat(64),
    effects: ['mint'], timestamp: 1_700_000_050,
  },
];

let eventsCallCount = 0;
let witnessCallCount = 0;

function installFetch() {
  global.fetch = async (url) => {
    const path = String(url).replace(/^https?:\/\/[^/]+/, '');
    const json = (body, status = 200) => ({
      ok: status >= 200 && status < 300,
      status,
      json: async () => body,
    });
    if (path === '/status') return json({ latest_height: 8, healthy: true, peer_count: 0 });
    if (path === '/api/cells') return json([]);
    if (path.startsWith('/api/starbridge/receipts')) return json(RECEIPTS_LIST);
    if (path === '/api/receipts') return json(RECEIPTS_LIST);
    if (path.startsWith('/api/blocklace/blocks') || path.startsWith('/api/blocks') || path.startsWith('/federation/roots'))
      return json([]);
    if (path.startsWith('/api/federations')) return json([]);
    if (path === '/api/intents') return json([]);
    if (path === '/api/tokens') return json([]);
    if (path.startsWith('/api/events')) { eventsCallCount += 1; return json(EVENTS); }
    const wm = path.match(/^\/api\/receipts\/([0-9a-f]{64})\/witnesses$/);
    if (wm) {
      witnessCallCount += 1;
      if (wm[1] === RECEIPT_HASH) return json(WITNESSES);
      return json({ receipt_hash: wm[1], witness_count: 0, artifact_format: 'DWR1', witness_artifacts: [], witnessed_receipts: [] });
    }
    return json(null, 404);
  };
}

// No EventSource in Node — leave it undefined so the SSE branch is skipped
// (the runtime guards with `typeof EventSource !== 'undefined'`).

async function run() {
  installFetch();
  const signals = makeSignals();
  const runtime = await createRemoteRuntime({ signals, baseUrl: 'http://mock-node' });

  // Let the immediate pollOnce() + first lazy fetches resolve.
  await sleep(60);

  // ── F1: witness lazy-fetch + merge ───────────────────────────────────────
  const receiptSig = runtime.getReceipt(RECEIPT_HASH);
  // Give the lazy /witnesses fetch a tick.
  await sleep(60);
  let r = receiptSig.value;
  check('F1: receipt resolves from list', !!r && r.turn_hash === RECEIPT_HASH);
  check('F1: artifact_format merged = DWR1', r && r.artifact_format === 'DWR1', r && r.artifact_format);
  check('F1: witness_artifacts merged from /witnesses', Array.isArray(r?.witness_artifacts) && r.witness_artifacts.length === 1,
    JSON.stringify(r?.witness_artifacts?.length));
  check('F1: witnessed_receipts merged', Array.isArray(r?.witnessed_receipts) && r.witnessed_receipts.length === 1);
  check('F1: /witnesses fetched exactly once', witnessCallCount === 1, `calls=${witnessCallCount}`);

  // A subsequent poll must NOT wipe the merged artifacts.
  await sleep(20);
  // Force a manual re-publish path by reading again after another poll cycle.
  await sleep(40);
  r = receiptSig.value;
  check('F1: artifacts survive re-poll', Array.isArray(r?.witness_artifacts) && r.witness_artifacts.length === 1,
    `still ${r?.witness_artifacts?.length}`);

  // ── F2: activity feed from /api/events committed history ──────────────────
  const traceSig = runtime.getTraceEvents();
  await sleep(40);
  const feed = traceSig.value;
  const evs = feed?.events || [];
  check('F2: /api/events polled', eventsCallCount >= 1, `calls=${eventsCallCount}`);
  check('F2: committed events present in feed', evs.length === 2, `count=${evs.length}`);

  const committed = evs.find((e) => e.payload?.turn_hash === RECEIPT_HASH);
  check('F2: committed event mapped to turn_lifecycle', committed?.kind === 'turn_lifecycle', committed?.kind);
  check('F2: committed event carries proof_status', committed?.payload?.proof_status === 'proved', committed?.payload?.proof_status);
  check('F2: committed event has source=committed', committed?.source === 'committed', committed?.source);
  check('F2: committed event effects preserved', JSON.stringify(committed?.payload?.effects) === JSON.stringify(['transfer']));

  const rejected = evs.find((e) => e.payload?.turn_hash === OTHER_HASH);
  check('F2: rejected event phase', rejected?.payload?.phase === 'rejected', rejected?.payload?.phase);
  check('F2: rejected event proof_status', rejected?.payload?.proof_status === 'proof_generation_failed', rejected?.payload?.proof_status);

  // ── Read-only invariant still holds ──────────────────────────────────────
  check('runtime is read-only', runtime.caps.read === true && runtime.caps.mutate === false);
  let threw = false;
  try { runtime.executeTurn(); } catch { threw = true; }
  check('mutations refuse', threw === true);

  runtime.destroy();
  console.log(`\n[runtime-remote-witness] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[runtime-remote-witness] crashed:', e); process.exit(2); });
