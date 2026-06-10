/**
 * Explorer TIME TRAVEL + labeled SAMPLE-mode smoke test.
 *
 * Verifies the two explorer upgrades:
 *   1. OFFLINE FALLBACK is opt-in and loudly labeled: with no reachable node
 *      the chrome says "offline" and a banner OFFERS the sample snapshot;
 *      after the user clicks, the chrome says "SAMPLE DATA" and the banner
 *      stays (never a silent substitution).
 *   2. RECEIPT TIME TRAVEL: the Time-travel page mounts <dregg-cell-history>
 *      for the sample escrow cell — the receipt chain renders with pre→post
 *      state commitments, a scrubber, and stepping backward changes the
 *      selected receipt.
 *
 * Runs entirely offline (points the explorer at an unreachable node port) so
 * it exercises exactly the fallback path. The live-node path is covered by
 * explorer-smoke.mjs.
 *
 * Prereqs: dist served on :8080  →  npx serve dist -l 8080
 * Run:     node tests/explorer-time-travel.mjs
 * Env:     EXPLORER_BASE (default http://localhost:8080)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.EXPLORER_BASE || 'http://localhost:8080';
// Deliberately unreachable: this test is about the offline path.
const DEAD_NODE = 'http://127.0.0.1:1';

// Must match explorer/sample-data.js sid('e5c0', 1).
const ESCROW = 'e5c01000'.repeat(8);

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  const errors = [];
  page.on('pageerror', (e) => errors.push(`pageerror: ${e.message}`));

  await page.addInitScript((url) => {
    localStorage.setItem('dregg_node_url', url);
    localStorage.setItem('dregg_auto_refresh', 'false');
  }, DEAD_NODE);
  await page.goto(`${BASE}/explorer/`, { waitUntil: 'domcontentloaded' });
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });

  // 1. offline chrome + the opt-in banner
  await page.waitForFunction(() => {
    const el = document.getElementById('connection-status');
    return el && el.classList.contains('error');
  }, { timeout: 20000 });
  check('offline chrome shows', true);

  const banner = page.locator('#sample-banner');
  await banner.waitFor({ state: 'visible', timeout: 10000 });
  const enterVisible = await page.locator('#sample-enter-btn').isVisible();
  check('sample banner offers (does not auto-enter)', enterVisible);

  // No sample objects before opting in.
  const preOptIn = await page.evaluate(() => {
    const app = document.getElementById('explorer-app');
    return app?.runtime?.sample === true;
  });
  check('runtime is NOT sample before opt-in', preOptIn === false);

  // 2. opt in → loudly labeled
  await page.click('#sample-enter-btn');
  await page.waitForFunction(() => {
    const el = document.getElementById('connection-status');
    return el && el.classList.contains('sample');
  }, { timeout: 10000 });
  const chromeLabel = await page.locator('#connection-status .ex-connection__label').textContent();
  check('chrome says SAMPLE DATA', /SAMPLE/i.test(chromeLabel || ''), chromeLabel);
  const bannerStays = await banner.isVisible();
  check('banner persists in sample mode', bannerStays);
  const isSampleRuntime = await page.evaluate(() => {
    const app = document.getElementById('explorer-app');
    return app?.runtime?.sample === true && /SAMPLE/i.test(app?.runtime?.sampleNote || '');
  });
  check('runtime carries sample:true + labeled note', isSampleRuntime);

  // 3. time travel on the sample escrow cell
  await page.click('[data-page="history"]');
  await page.fill('#history-cell-input', ESCROW);
  await page.click('#history-walk-btn');

  const history = page.locator('dregg-cell-history');
  await history.waitFor({ state: 'attached', timeout: 10000 });
  await page.waitForFunction(() => {
    const el = document.querySelector('dregg-cell-history');
    return el && /post-state/i.test(el.textContent || '');
  }, { timeout: 15000 });
  check('<dregg-cell-history> renders commitments', true);

  const headBadge = await page.locator('dregg-cell-history .dregg-ch__pill--head').count();
  check('starts at HEAD', headBadge >= 1);

  const beforeTurn = await page.evaluate(() => {
    const code = document.querySelector('dregg-cell-history .dregg-inspector__kv code');
    return code ? code.textContent : null;
  });
  // step backward
  const olderBtn = page.locator('dregg-cell-history button', { hasText: 'older' }).first();
  await olderBtn.click();
  await page.waitForTimeout(300);
  const afterTurn = await page.evaluate(() => {
    const code = document.querySelector('dregg-cell-history .dregg-inspector__kv code');
    return code ? code.textContent : null;
  });
  check('stepping older changes the selected receipt', beforeTurn !== afterTurn, `${beforeTurn} → ${afterTurn}`);

  const chainRows = await page.locator('dregg-cell-history table tbody tr').count();
  check('full chain table lists multiple receipts', chainRows >= 2, `${chainRows} rows`);

  // honesty copy: commitments-not-slot-values note present
  const honest = await page.evaluate(() => {
    const el = document.querySelector('dregg-cell-history');
    return /not historical slot values/i.test(el?.textContent || '');
  });
  check('honest commitments-only scope note present', honest);

  const fatal = errors.filter((e) => !/favicon|net::|Failed to fetch|NetworkError|CORS/i.test(e));
  check('no page errors', fatal.length === 0, fatal.join(' | '));

  await browser.close();
  console.log(failures ? `\n${failures} FAILURE(S)` : '\nALL PASS');
  process.exit(failures ? 1 : 0);
}

run().catch((e) => { console.error(e); process.exit(1); });
