/**
 * Starbridge SHELL smoke test (site side).
 *
 * Pins the shell contract at /starbridge/:
 *
 *   1. Boot sequence: with an unreachable node (?node=http://127.0.0.1:9)
 *      the Connect stage appears; "continue anyway" → Identity stage;
 *      "continue as guest" → home mounts inside the frame.
 *   2. The persistent frame: rail sections (identity, places, your cells,
 *      receipt stream, node state) all exist after boot.
 *   3. Places: navigating to #/place/nameservice mounts the embedded app
 *      frame (?embedded=1) WITHOUT a page load (the shell is one document).
 *   4. The command affordance: ctrl-K opens the palette; typing a 64-hex id
 *      offers an inspect jump; Escape closes it.
 *   5. Identity provisioning: "New identity" generates a 24-word phrase and
 *      derives a key + cell id in-browser (wasm Ed25519 + the verified JS
 *      BLAKE3 derive_raw path); the rail then shows the named profile.
 *      (The faucet claim is expected to FAIL here — the node is unreachable —
 *      and must surface as a note, never as a fabricated success.)
 *
 * Prereqs:  dist served on :8080  →  npx serve dist -l 8080
 * Run:      node tests/shell-smoke.mjs
 * Env:      STARBRIDGE_BASE (default http://localhost:8080)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.STARBRIDGE_BASE || 'http://localhost:8080';
const DEAD_NODE = 'http://127.0.0.1:9';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));
  page.on('console', (msg) => {
    if (msg.type() !== 'error') return;
    const text = msg.text();
    // The dead node produces expected fetch/EventSource failures; everything
    // else is a real error.
    if (/127\.0\.0\.1:9|Failed to load resource|ERR_CONNECTION|Failed to fetch|NetworkError|fetchCellInto|api\/events/i.test(text)) return;
    errors.push(text);
  });

  await page.goto(`${BASE}/starbridge/?node=${encodeURIComponent(DEAD_NODE)}`, {
    waitUntil: 'domcontentloaded',
  });
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });

  // ── 1. boot: connect stage on unreachable node ────────────────────────────
  await page.waitForSelector('#shl-boot:not([hidden])', { timeout: 20000 });
  await page.waitForSelector('#shl-boot-body [data-act="skip"]', { timeout: 20000 });
  check('boot shows the Connect stage when the node is unreachable', true);
  const statusOk = await page.getAttribute('.shl-boot__status', 'data-ok');
  check('connect stage reports unreachable honestly', statusOk === 'false');

  await page.click('#shl-boot-body [data-act="skip"]');
  await page.waitForSelector('#shl-boot-body [data-act="guest"]', { timeout: 10000 });
  check('identity stage follows', true);

  // ── 5a. identity provisioning (before guest path, on the same stage) ─────
  await page.click('#shl-boot-body [data-act="create"]');
  const phrase = await page.inputValue('#shl-boot-body [name="phrase"]');
  check('a 24-word phrase is generated', phrase.trim().split(/\s+/).length === 24, phrase.slice(0, 40) + '…');
  await page.fill('#shl-boot-body [name="name"]', 'smoke');
  await page.click('#shl-boot-body button[type="submit"]');

  // wasm download + keypair + cell-id derivation, then home.
  await page.waitForFunction(() => document.getElementById('shl-boot')?.hidden === true, { timeout: 60000 });
  check('identity created and the shell booted to home', true);

  const idName = await page.textContent('#shl-identity .shl-id__name');
  check('rail identity card names the profile', (idName || '').trim() === 'smoke', idName || '');
  const cellLink = await page.getAttribute('#shl-identity .shl-id__detail a', 'href');
  check('rail identity links the derived cell', /#\/inspect\/dregg%3A%2F%2Fcell%2F[0-9a-f]/.test(cellLink || ''), cellLink || '');

  // ── 2. the persistent frame ───────────────────────────────────────────────
  for (const sel of ['#shl-identity', '#shl-places', '#shl-cells', '#shl-stream', '#shl-node']) {
    const present = await page.$(sel);
    check(`rail section ${sel} present`, !!present);
  }
  const streamMode = await page.textContent('.shl-stream__mode').catch(() => '');
  check('receipt stream states its (un)reachability', /no events reachable|polling|live/.test(streamMode || ''), streamMode || '');
  const homeLede = await page.textContent('.shl-home__lede');
  check('home says who you are', /smoke/.test(homeLede || ''));

  // ── 3. places mount in-frame ──────────────────────────────────────────────
  const navCount = await page.evaluate(() => window.performance.getEntriesByType('navigation').length);
  await page.click('#shl-places a[href="#/place/nameservice"]');
  await page.waitForSelector('iframe.shl-place__frame', { timeout: 15000 });
  const frameSrc = await page.getAttribute('iframe.shl-place__frame', 'src');
  check('place mounts the embedded app frame', /embedded=1/.test(frameSrc || ''), frameSrc || '');
  const navCountAfter = await page.evaluate(() => window.performance.getEntriesByType('navigation').length);
  check('no full-page navigation occurred', navCount === navCountAfter);
  const railStill = await page.$('#shl-stream');
  check('the rail persists around the place', !!railStill);

  // ── 3b. the operational organs surface ────────────────────────────────────
  // The rail carries an Organs group; the home view carries organ cards. The
  // four organs (trustline / channel / mailbox / court) each have a registered
  // inspector that reads the node-side status route — and degrades honestly to
  // "node-only" when there is no connected node (the dead node here).
  await page.evaluate(() => { window.location.hash = '#/home'; });
  await page.waitForSelector('.shl-home__grid--organs', { timeout: 8000 });
  const organCards = await page.$$('.shl-home__grid--organs .shl-card--organ');
  check('home surfaces the four organs', organCards.length === 4, `cards=${organCards.length}`);
  for (const tag of ['dregg-trustline', 'dregg-channel', 'dregg-mailbox', 'dregg-court']) {
    const registered = await page.evaluate((t) => !!customElements.get(t), tag);
    check(`organ inspector ${tag} is registered`, registered);
  }
  const railOrganBtns = await page.$$('#shl-places [data-organ]');
  check('rail Organs group offers all four', railOrganBtns.length === 4, `btns=${railOrganBtns.length}`);

  // Open the channel organ inspector by id (a dialog prompt supplies the id).
  const fakeId = 'ab'.repeat(32);
  page.once('dialog', (d) => d.accept(fakeId));
  await page.click('#shl-places [data-organ="channel"]');
  await page.waitForSelector('dregg-channel', { timeout: 8000 });
  const channelText = await page.textContent('dregg-channel').catch(() => '');
  check('channel inspector mounts and is honest off a node',
    /node-only|unreachable|Connect a node|epochs/i.test(channelText || ''), (channelText || '').slice(0, 80));

  // ── 4. the command affordance ─────────────────────────────────────────────
  await page.keyboard.press('Control+k');
  await page.waitForSelector('.shl-palette:not([hidden])', { timeout: 5000 });
  check('ctrl-K opens the palette', true);
  await page.fill('.shl-palette__input', 'a'.repeat(64));
  const itemText = await page.textContent('.shl-palette__item');
  check('a 64-hex query offers an inspect jump', /inspect cell/.test(itemText || ''), itemText || '');
  await page.keyboard.press('Escape');
  await page.waitForFunction(() => document.querySelector('.shl-palette')?.hidden === true, { timeout: 5000 });
  check('escape closes the palette', true);

  // ── 5b. derive_raw oracle: JS BLAKE3 vs the real Rust path (wasm) ─────────
  // wasm create_cell computes CellId::derive_raw(pk, blake3(domain)) with the
  // SAME Rust code the node runs (domain "dregg-wasm-default-domain" instead
  // of "default"). The shell's JS derivation must agree byte-for-byte on the
  // composition; the "default"-domain case is then the same function applied
  // to a different token id.
  const oracle = await page.evaluate(async () => {
    const wasm = await import('/pkg/dregg_wasm.js');
    await wasm.default();
    const b3 = await import('/_includes/studio/shell/blake3.js');
    const pkHex = '11'.repeat(32);
    const h = wasm.create_runtime();
    wasm.create_agent(h, 'oracle', 1000000n);
    const got = wasm.create_cell(h, pkHex, 0n).cell_id;
    wasm.destroy_runtime(h);
    const token = b3.blake3Hash('dregg-wasm-default-domain');
    const material = new Uint8Array(64);
    material.set(b3.hexToBytes(pkHex), 0);
    material.set(token, 32);
    const expected = b3.bytesToHex(b3.blake3DeriveKey('dregg-cell-id-v1', material));
    return { got, expected };
  });
  check('JS derive_raw agrees with the Rust wasm derivation',
    oracle.got === oracle.expected, `${oracle.got} vs ${oracle.expected}`);

  // ── console hygiene ───────────────────────────────────────────────────────
  check('no unexpected console/page errors', errors.length === 0, errors.slice(0, 3).join(' | '));

  await browser.close();
  console.log(failures ? `\n${failures} failure(s)` : '\nshell smoke: all green');
  process.exit(failures ? 1 : 0);
}

run().catch((e) => { console.error(e); process.exit(1); });
