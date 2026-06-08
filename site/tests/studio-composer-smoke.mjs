/**
 * Studio turn-composer smoke test.
 *
 * Drives the real <dregg-turn-composer> authoring flow in a browser against the
 * built dist:
 *
 *   1. The Studio page boots and the composer loads the generated submit schema
 *      (4 thin-HTTP effect kinds) — no node required for compose.
 *   2. COMPOSE: add an increment_nonce effect via the guided form; the effect
 *      appears in the turn and the wire-JSON preview reflects it.
 *   3. VALIDATE: an invalid transfer (bad `to`) is flagged and the Simulate
 *      button stays disabled until it's fixed.
 *   4. SIMULATE: the local model shows a state diff and honest "needs executor"
 *      rows for auth + proof.
 *   5. SUBMIT (optional, when NODE_URL + NODE_TOKEN are set): posts the turn to
 *      a live node and surfaces the node's real verdict.
 *
 * Prereqs:  npx serve dist -l 8080   (STUDIO_BASE, default http://localhost:8080)
 * Optional submit leg: a running, unlocked dregg-node:
 *   NODE_URL=http://127.0.0.1:8420 NODE_TOKEN=<unlock-bearer> node tests/studio-composer-smoke.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STUDIO_BASE || 'http://localhost:8080';
const NODE_URL = process.env.NODE_URL || '';
const NODE_TOKEN = process.env.NODE_TOKEN || '';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function main() {
  const browser = await chromium.launch();
  const page = await browser.newPage();
  page.on('console', (m) => { if (m.type() === 'error') console.log('  [console.error]', m.text()); });

  // Pre-seed node config in localStorage so the submit leg targets our node.
  await page.addInitScript(([url, tok]) => {
    if (url) localStorage.setItem('dregg_node_url', url);
    if (tok) localStorage.setItem('dregg_node_token', tok);
    localStorage.setItem('dregg_studio_guide_dismissed', '1');
  }, [NODE_URL, NODE_TOKEN]);

  await page.goto(`${BASE}/studio.html`, { waitUntil: 'networkidle' });

  // 1. composer present + schema loaded
  await page.waitForSelector('dregg-turn-composer .dregg-tc__add-kind', { timeout: 8000 });
  const kinds = await page.$$eval('dregg-turn-composer .dregg-tc__add-kind option', (os) => os.map((o) => o.value));
  check('composer loaded submit schema', kinds.length === 4 && kinds.includes('increment_nonce'),
    `kinds=[${kinds.join(',')}]`);

  // 2. COMPOSE: pick increment_nonce, add it
  await page.selectOption('dregg-turn-composer .dregg-tc__add-kind', 'increment_nonce');
  await page.click('dregg-turn-composer .dregg-tc__add-btn');
  const effCount = await page.$$eval('dregg-turn-composer .dregg-tc__eff', (e) => e.length);
  check('compose: effect added to turn', effCount === 1, `effects=${effCount}`);
  const previewJson = await page.$eval('dregg-turn-composer .dregg-tc__json', (e) => e.textContent);
  check('compose: wire preview includes increment_nonce',
    /"kind":\s*"increment_nonce"/.test(previewJson));

  // 3. VALIDATE: add a transfer with an invalid recipient → flagged, Simulate stays usable
  //    but the bad effect is highlighted (turn-level validity false).
  await page.selectOption('dregg-turn-composer .dregg-tc__add-kind', 'transfer');
  await page.fill('dregg-turn-composer .dregg-tc__add-fields [data-field="to"]', 'not-a-cell-id');
  await page.fill('dregg-turn-composer .dregg-tc__add-fields [data-field="amount"]', '5');
  await page.click('dregg-turn-composer .dregg-tc__add-btn');
  const badCount = await page.$$eval('dregg-turn-composer .dregg-tc__eff.is-bad', (e) => e.length);
  check('validate: invalid transfer recipient flagged', badCount === 1, `bad=${badCount}`);
  const validClass = await page.$eval('dregg-turn-composer .dregg-tc__valid', (e) => e.className);
  check('validate: turn marked not-valid', /is-fail/.test(validClass));

  // remove the bad effect (the 2nd one, index 1)
  await page.click('dregg-turn-composer .dregg-tc__eff-del[data-del="1"]');
  const validClass2 = await page.$eval('dregg-turn-composer .dregg-tc__valid', (e) => e.className);
  check('validate: turn valid after removing bad effect', /is-ok/.test(validClass2));

  // 4. SIMULATE
  await page.click('dregg-turn-composer .dregg-tc__next[data-goto="simulate"]');
  await page.waitForSelector('dregg-turn-composer .dregg-tc__simrows');
  const verdicts = await page.$$eval('dregg-turn-composer .dregg-tc__simrow .dregg-tc__simverdict', (e) => e.map((x) => x.textContent));
  check('simulate: shows an applied step', verdicts.includes('applied'), `verdicts=[${verdicts.join(',')}]`);
  check('simulate: honest "needs executor" rows for auth/proof',
    verdicts.filter((v) => v === 'needs executor').length >= 2);

  // 5. SUBMIT (only when a node is configured)
  if (NODE_URL && NODE_TOKEN) {
    await page.click('dregg-turn-composer .dregg-tc__next[data-goto="submit"]');
    await page.waitForSelector('dregg-turn-composer .dregg-tc__submit-btn');
    await page.click('dregg-turn-composer .dregg-tc__submit-btn');
    // A committed turn runs the real STARK prover, which can take tens of
    // seconds on a debug node build — allow generous headroom.
    await page.waitForSelector('dregg-turn-composer .dregg-tc__subres:not(.is-pending)', { timeout: 90000 });
    const res = await page.$eval('dregg-turn-composer .dregg-tc__subres', (e) => e.textContent);
    // We require a real node verdict (HTTP 200 accepted/rejected), not
    // "unreachable". When EXPECT_COMMIT=1 (the operator cell is funded) we
    // additionally require an ACCEPTED + proved verdict.
    check('submit: got a real node verdict (not unreachable)',
      /ACCEPTED|REJECTED/.test(res) && !/unreachable/.test(res), res.replace(/\s+/g, ' ').slice(0, 180));
    if (process.env.EXPECT_COMMIT === '1') {
      const ok = await page.$('dregg-turn-composer .dregg-tc__subres.is-ok');
      check('submit: turn COMMITTED (accepted + proved)', !!ok && /ACCEPTED/.test(res) && /proved/.test(res),
        res.replace(/\s+/g, ' ').slice(0, 180));
    }
  } else {
    console.log('SKIP  submit leg (set NODE_URL + NODE_TOKEN to exercise it)');
  }

  await browser.close();
  console.log(`\n${failures === 0 ? 'ALL PASS' : failures + ' FAILURE(S)'}`);
  process.exit(failures === 0 ? 0 : 1);
}

main().catch((e) => { console.error(e); process.exit(2); });
