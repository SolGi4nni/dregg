/**
 * Explorer F1 (witnessed-receipt DWR1 artifacts) + F2 (activity proof_status)
 * in-browser render test against a MOCKED node (Playwright route interception).
 *
 * This proves the wiring end-to-end in a real browser without a live node:
 *   - /api/receipts/{hash}/witnesses returns DWR1 artifacts → opening the
 *     receipt mounts <dregg-witnessed-receipt> showing "Scope-2" + the artifact.
 *   - /api/events returns committed history with proof_status → <dregg-activity>
 *     renders the backlog with a proof-status badge ("proved").
 *
 * Run:  node tests/explorer-witness-activity.mjs
 * Env:  EXPLORER_BASE (default http://localhost:8080)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.EXPLORER_BASE || 'http://localhost:8080';
const NODE = 'http://mock-node.local';

const RECEIPT_HASH = 'a'.repeat(64);
const CELL = 'c'.repeat(64);

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const json = (route, body) =>
  route.fulfill({ status: 200, contentType: 'application/json', body: JSON.stringify(body) });

async function installNodeMock(ctx) {
  await ctx.route(`${NODE}/**`, async (route) => {
    const url = new URL(route.request().url());
    const p = url.pathname;
    if (p === '/status') return json(route, { latest_height: 8, healthy: true, peer_count: 0, federation_mode: 'solo' });
    if (p === '/api/cells') return json(route, [{ id: CELL, balance: 1000, nonce: 0, capability_count: 0, found: true }]);
    if (p === '/api/starbridge/receipts' || p === '/api/receipts')
      return json(route, [{
        receipt_hash: RECEIPT_HASH, turn_hash: RECEIPT_HASH, agent: CELL,
        pre_state: '1'.repeat(64), post_state: '2'.repeat(64),
        timestamp: 1700000000, computrons_used: 42, action_count: 1,
        has_proof: true, has_witness: true, witness_count: 1,
      }]);
    if (p === `/api/receipts/${RECEIPT_HASH}/witnesses`)
      return json(route, {
        receipt_hash: RECEIPT_HASH, witness_count: 1, artifact_format: 'DWR1',
        witness_artifacts: ['44575231' + 'de'.repeat(40)],
        witnessed_receipts: [{ kind: 'WitnessedReceipt' }],
      });
    if (p.startsWith('/api/receipts/') && p.endsWith('/witnesses'))
      return json(route, { receipt_hash: '', witness_count: 0, artifact_format: 'DWR1', witness_artifacts: [], witnessed_receipts: [] });
    if (p === '/api/events')
      return json(route, [{
        height: 7, status: 'committed', proof_status: 'proved',
        turn_hash: RECEIPT_HASH, cell_id: CELL, effects: ['transfer'], timestamp: 1700000000,
      }]);
    if (p === '/api/blocklace/blocks' || p === '/api/blocks' || p === '/federation/roots') return json(route, []);
    if (p === '/api/federations') return json(route, []);
    if (p === '/api/intents') return json(route, []);
    if (p === '/api/tokens') return json(route, []);
    if (p === '/observability/stream')
      return route.fulfill({ status: 200, contentType: 'text/event-stream', body: '' });
    return json(route, null);
  });
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  await installNodeMock(ctx);
  const page = await ctx.newPage();
  const pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));

  await page.addInitScript((url) => {
    localStorage.setItem('dregg_node_url', url);
    localStorage.setItem('dregg_auto_refresh', 'true');
  }, NODE);

  // ── F1: open the receipt → witnessed-receipt with DWR1 artifact ───────────
  await page.goto(`${BASE}/explorer/?at=${encodeURIComponent(`dregg://receipt/${RECEIPT_HASH}`)}`,
    { waitUntil: 'domcontentloaded' });
  await page.waitForFunction(() => {
    const app = document.getElementById('explorer-app');
    return app && app.runtime && app.runtime.caps;
  }, { timeout: 20000 });

  await page.waitForSelector('dregg-witnessed-receipt', { timeout: 10000 });
  // Wait for the lazy /witnesses fetch to merge artifacts and the scope-2 pane to render.
  await page.waitForFunction(() => {
    const el = document.querySelector('dregg-witnessed-receipt');
    return el && /scope-2/i.test(el.textContent || '');
  }, { timeout: 15000 }).catch(() => {});
  const wrText = await page.evaluate(() =>
    document.querySelector('dregg-witnessed-receipt')?.textContent || '');
  check('F1: witnessed-receipt mounts for a receipt', wrText.length > 0);
  check('F1: shows Scope-2 (DWR1 artifacts merged)', /scope-2/i.test(wrText), wrText.replace(/\s+/g, ' ').slice(0, 90));
  check('F1: shows artifact_format DWR1', /DWR1/i.test(wrText));

  // ── F2: activity page → committed backlog with proof_status badge ─────────
  await page.click('[data-page="activity"]');
  await page.waitForSelector('#mount-activity dregg-activity', { timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('#mount-activity dregg-activity');
    return el && /committed/i.test(el.textContent || '');
  }, { timeout: 15000 }).catch(() => {});
  const actText = await page.evaluate(() =>
    document.querySelector('#mount-activity dregg-activity')?.textContent || '');
  check('F2: activity shows committed backlog', /committed/i.test(actText), actText.replace(/\s+/g, ' ').slice(0, 90));
  check('F2: activity shows proof_status badge (proved)', /proved/i.test(actText));
  check('F2: activity shows live-node tier (not sim)', /live node/i.test(actText));

  check('no uncaught page errors', pageErrors.length === 0, pageErrors.join(' | '));

  await browser.close();
  console.log(`\n[explorer-witness-activity] ${failures === 0 ? 'ALL PASSED' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => { console.error('[explorer-witness-activity] crashed:', e); process.exit(2); });
