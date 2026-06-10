/**
 * Browser smoke test for the polis inspectors — <dregg-council> /
 * <dregg-constitution> in DESCRIPTOR (factory-view) mode, fed the GENERATED
 * council/constitution samples (produced by running the real Rust
 * constructors). Verifies the element renders the machine + charter terms
 * decoded FROM the descriptor: the 2-of-3 threshold, the state diagram with
 * DRAFT lit at birth, the pinned constitution parameters, and the
 * About-this-object provenance panel.
 *
 * Prereqs: dist served on :8080  →  npx serve dist -l 8080
 * Run:     node tests/studio/polis-inspector-dom.mjs
 * Env:     BASE (default http://localhost:8080)
 */

import { chromium } from '../../node_modules/playwright/index.mjs';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const BASE = process.env.BASE || 'http://localhost:8080';
const HERE = path.dirname(fileURLToPath(import.meta.url));
const SAMPLES = JSON.parse(fs.readFileSync(
  path.join(HERE, '..', '..', 'src', '_includes', 'studio', 'factory-samples.generated.json'), 'utf8'));

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch();
  const page = await browser.newContext().then((c) => c.newPage());
  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));

  // The studio page loads runtime-bootstrap (dreggUi) + the inspectors barrel.
  await page.goto(`${BASE}/studio.html`, { waitUntil: 'domcontentloaded' });
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  await page.waitForFunction(() => !!customElements.get('dregg-council'), { timeout: 20000 });

  // ── <dregg-council> in factory view on the generated 2-of-3 sample ─────────
  await page.evaluate((desc) => {
    const el = document.createElement('dregg-council');
    el.setAttribute('mode', 'descriptor');
    el.setAttribute('data-descriptor', JSON.stringify(desc));
    el.id = 'test-council';
    document.body.appendChild(el);
  }, SAMPLES.council.descriptor);
  await page.waitForSelector('#test-council .dregg-polis', { timeout: 10000 });
  const councilText = await page.textContent('#test-council');

  check('council inspector renders', councilText.includes('council proposal'));
  check('charter decodes 2-of-3 from the AffineLe gate', councilText.includes('2-of-3'));
  check('factory view honestly labeled', councilText.includes('FACTORY VIEW'));
  const states = await page.$$eval('#test-council .dregg-polis__state', (els) => els.map((e) => e.textContent.trim()));
  check('machine renders all five states', ['DRAFT', 'PROPOSED', 'APPROVED', 'EXECUTED', 'REJECTED'].every((s) => states.includes(s)), states.join(','));
  const lit = await page.$eval('#test-council .dregg-polis__state.is-lit', (e) => e.textContent.trim());
  check('birth state DRAFT is lit', lit === 'DRAFT', lit);
  const terminals = await page.$$eval('#test-council .dregg-polis__state.is-terminal', (els) => els.map((e) => e.textContent.trim()));
  check('REJECTED + EXECUTED marked terminal', terminals.includes('REJECTED') && terminals.includes('EXECUTED'), terminals.join(','));
  check('About panel names the decoder provenance', councilText.includes('inspect_council') && councilText.includes('starbridge-apps/polis'));

  // ── <dregg-constitution> factory view on the generated v1 sample ───────────
  await page.evaluate((desc) => {
    const el = document.createElement('dregg-constitution');
    el.setAttribute('mode', 'descriptor');
    el.setAttribute('data-descriptor', JSON.stringify(desc));
    el.id = 'test-constitution';
    document.body.appendChild(el);
  }, SAMPLES.constitution.descriptor);
  await page.waitForSelector('#test-constitution .dregg-polis', { timeout: 10000 });
  const constText = await page.textContent('#test-constitution');
  check('constitution inspector renders', constText.includes('constitution'));
  check('pinned parameters decode (delay 1024, cap 10000)', constText.includes('1024') && constText.includes('10000'));
  check('pinned-for-life teeth stated', constText.includes('pinned for life'));
  const cLit = await page.$eval('#test-constitution .dregg-polis__state.is-lit', (e) => e.textContent.trim());
  check('constitution birth state UNINIT lit', cLit === 'UNINIT', cLit);

  // ── compose-then-inspect round trip in the real composer ───────────────────
  // (no .html here: `serve`'s clean-URL redirect drops query strings; the
  // production static hosts serve /studio.html?… directly)
  await page.goto(`${BASE}/studio?factory=council#factory`, { waitUntil: 'domcontentloaded' });
  await page.waitForSelector('dregg-factory-composer .dregg-fc', { timeout: 20000 });
  await page.waitForSelector('.dregg-fc__inspect', { timeout: 20000 });
  const fcText = await page.textContent('dregg-factory-composer');
  check('?factory=council deep link loads the worked example', fcText.includes('Loaded council') || fcText.includes('council'));
  check('composer recognizes its own constraint set as a council machine', fcText.includes('recognizable'));
  await page.waitForSelector('.dregg-fc__inspect dregg-council .dregg-polis', { timeout: 20000 });
  const embedded = await page.textContent('.dregg-fc__inspect dregg-council');
  check('embedded inspector decodes the composed descriptor (2-of-3)', embedded.includes('2-of-3'));

  const benign = (m) => /favicon|esm\.sh|net::|Failed to fetch|fetch.*8420/i.test(m);
  const real = errors.filter((m) => !benign(m));
  check('no page errors', real.length === 0, real.slice(0, 3).join(' | '));

  await browser.close();
  if (failures) { console.error(`\n${failures} FAILURE(S)`); process.exit(1); }
  console.log('\nALL PASS');
}

run().catch((e) => { console.error(e); process.exit(1); });
