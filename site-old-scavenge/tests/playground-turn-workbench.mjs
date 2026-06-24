/**
 * Playground TURN WORKBENCH smoke test — the verb-first turn surface.
 *
 * Verifies, against the REAL wasm runtime (no fakes):
 *   1. The section renders the eight dregg3 verbs.
 *   2. EXPLAIN-BEFORE-RUN: a staged effect shows its verified-Lean semantics +
 *      authority facet + wire mnemonic from ontology-catalog.generated.json.
 *   3. RUN LOCALLY: execute_turn commits a real turn — receipt with turn_hash
 *      and pre→post state commitments rendered.
 *   4. PROVE: prove_turn produces a real EffectVM STARK (size + trace rows).
 *   5. The WASM-gaps panel documents the missing explain/blocklace bindings
 *      (honest inventory, not stubbed success).
 *   6. grant is labeled local-only (no thin-HTTP projection).
 *
 * Prereqs: dist served on :8080  →  npx serve dist -l 8080
 * Run:     node tests/playground-turn-workbench.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const BASE = process.env.BASE || 'http://localhost:8080';
const HERE = path.dirname(fileURLToPath(import.meta.url));
const ONTOLOGY = JSON.parse(fs.readFileSync(
  path.join(HERE, '..', 'src', '_includes', 'studio', 'ontology-catalog.generated.json'), 'utf8'));

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

  await page.goto(`${BASE}/playground/#turn-workbench`, { waitUntil: 'domcontentloaded' });
  // wasm load can take a moment
  await page.waitForFunction(() => {
    const el = document.getElementById('wasm-status');
    return el && /ready|error/.test(el.textContent || '');
  }, { timeout: 60000 });
  const wasmReady = await page.evaluate(() => /ready/.test(document.getElementById('wasm-status')?.textContent || ''));
  check('wasm loaded', wasmReady);

  const section = page.locator('#section-turn-workbench');
  await page.waitForFunction(() => {
    const s = document.getElementById('section-turn-workbench');
    return s && s.querySelectorAll('.twb-verb').length >= 8;
  }, { timeout: 20000 });
  const verbCount = await section.locator('.twb-verb').count();
  check('eight verbs in the palette', verbCount === 8, `${verbCount}`);

  // 2. stage a write (set_field) and check the explain panel quotes the catalog
  await section.locator('[data-verb="write"]').click();
  await section.locator('[data-stage="set_field"]').click();
  await page.waitForSelector('#section-turn-workbench .twb-staged');

  const setFieldCat = ONTOLOGY.effects.find((e) => e.ctor === 'setFieldA');
  const explainText = await section.locator('.twb-staged__explain').first().textContent();
  check('explain quotes the Lean catalog semantics',
    explainText.includes(setFieldCat.semantics.slice(0, 40)), explainText.slice(0, 80));
  const facet = await section.locator('.twb-pill--facet').first().textContent();
  check('authority facet shown from catalog', facet.trim() === setFieldCat.facet, `${facet} vs ${setFieldCat.facet}`);

  // 3. run locally (real execute_turn)
  await section.locator('#twb-run').click();
  await page.waitForFunction(() => {
    const s = document.getElementById('section-turn-workbench');
    return s && /COMMITTED|REJECTED|ERROR/.test(s.textContent || '');
  }, { timeout: 30000 });
  const committed = await page.evaluate(() => /COMMITTED/.test(document.getElementById('section-turn-workbench').textContent));
  check('execute_turn committed a real turn', committed);
  const hasCommitments = await page.evaluate(() =>
    /pre-state/.test(document.getElementById('section-turn-workbench').textContent) &&
    /post-state/.test(document.getElementById('section-turn-workbench').textContent));
  check('receipt shows pre→post state commitments', hasCommitments);

  // 4. prove it (real EffectVM STARK; generous budget — wasm proving is slow)
  await section.locator('#twb-prove').click();
  await page.waitForFunction(() => {
    const s = document.getElementById('section-turn-workbench');
    return s && (s.querySelector('.twb-proof') || s.querySelector('.twb-result .twb-err'));
  }, { timeout: 120000 });
  const proof = await page.evaluate(() => {
    const el = document.querySelector('#section-turn-workbench .twb-proof');
    return el ? el.textContent : null;
  });
  check('prove_turn produced a real proof', !!proof && /bytes/.test(proof), (proof || 'no proof').slice(0, 100));

  // 6. grant is labeled local-only
  await section.locator('[data-verb="grant"]').click();
  await section.locator('[data-stage="grant"]').click();
  await page.waitForTimeout(200);
  const localOnly = await section.locator('.twb-pill--warn', { hasText: 'local-only' }).count();
  check('grant labeled local-only (no thin-HTTP projection)', localOnly >= 1);

  // 5. gaps panel documents the missing bindings precisely
  const gaps = await page.evaluate(() => {
    const el = document.querySelector('#section-turn-workbench .twb-gaps');
    return el ? el.textContent : '';
  });
  check('gaps panel names sdk explain.rs missing binding', /explain_turn/.test(gaps) && /sdk\/src\/explain\.rs/.test(gaps));
  check('gaps panel names blocklace sync gap', /blocklace/.test(gaps));

  const fatal = errors.filter((e) => !/favicon|net::|Failed to fetch/i.test(e));
  check('no page errors', fatal.length === 0, fatal.join(' | ').slice(0, 300));

  await browser.close();
  console.log(failures ? `\n${failures} FAILURE(S)` : '\nALL PASS');
  process.exit(failures ? 1 : 0);
}

run().catch((e) => { console.error(e); process.exit(1); });
