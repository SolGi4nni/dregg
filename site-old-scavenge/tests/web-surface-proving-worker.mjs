/**
 * Web-surface proving-Worker + in-tab verify_history smoke test
 * (WEB-FORWARD §(a) + §(b)).
 *
 * Verifies, in a REAL headless browser against the built dist:
 *
 *   1. The proving Web Worker (`prove-worker.js`) loads as a module worker, inits
 *      its OWN wasm instance, and signals ready — proving runs OFF the main thread.
 *   2. The in-tab anti-pale-ghost tooth runs the REAL verify path with the trust
 *      anchor as CONFIG, not the artifact: `verify_devnet_history(envelope, anchor)`
 *      REFUSES when the envelope's claimed fingerprint ≠ the configured anchor
 *      (the anchor-discipline check), and the refusal names VkFingerprint/circuit.
 *      (This path is instant — no STARK proving — so it is smoke-test-fast; the
 *      full fold+verify `light_client_demo` is ~minutes and is exercised by the
 *      Rust `dregg-lightclient` tests + manual playground use.)
 *   3. The page main thread is NOT frozen while the worker holds wasm (a rAF tick
 *      lands within a frame budget) — the responsiveness property the Worker buys.
 *
 * Prereqs:  dist served (default http://localhost:8099)
 * Run:      node tests/web-surface-proving-worker.mjs
 * Env:      PLAYGROUND_BASE (default http://localhost:8099)
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.PLAYGROUND_BASE || 'http://localhost:8099';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));

  await page.goto(`${BASE}/playground/#web-surface`, { waitUntil: 'domcontentloaded' });

  // wasm bootstrap (the page-side instance the section uses for the typeof guard).
  await page
    .waitForFunction(
      () => document.getElementById('wasm-status')?.classList.contains('ready'),
      { timeout: 30000 },
    )
    .catch(() => {});

  // (1) The proving Worker loads, inits its own wasm, and answers a request.
  // We drive the ProvingClient directly (the same module the section imports) so
  // the test exercises the real worker plumbing, not a re-implementation.
  const workerReady = await page.evaluate(async (base) => {
    const mod = await import(`${base}/playground/proving-client.js`);
    const client = new mod.ProvingClient();
    // ready() resolves when the worker posts {ready:true} after wasm init.
    await client.ready();
    return true;
  }, BASE);
  check('proving Worker loads + inits its own wasm instance (off main thread)', workerReady === true);

  // (2) The config-not-artifact tooth: verify_devnet_history REFUSES a mismatch.
  // Build a versioned envelope claiming circuit "aa..", verify it against a
  // configured anchor "cc.." — the anchor-discipline check must refuse, and NEVER
  // attest. This is the real in-tab verify discipline (anchor = config argument).
  const refusal = await page.evaluate(async (base) => {
    const mod = await import(`${base}/playground/proving-client.js`);
    const client = new mod.ProvingClient();
    await client.ready();
    const envelope = JSON.stringify({
      version: 1,
      vk_fingerprint_hex: 'aa'.repeat(32), // the producer's CLAIMED circuit
      proof_bytes_b64: '',
      genesis_root: 1,
      final_root: 2,
      chain_digest: 3,
      num_turns: 2,
    });
    const configAnchor = 'cc'.repeat(32); // the client's OWN configured anchor (differs)
    const view = await client.verifyDevnetHistory(envelope, configAnchor);
    return view;
  }, BASE);
  check(
    'verify_devnet_history REFUSES when envelope claim ≠ configured anchor',
    refusal && refusal.attested === false,
    `attested=${refusal && refusal.attested}`,
  );
  check(
    'the refusal names the anchor-discipline (config-not-artifact), not a fake pass',
    refusal &&
      typeof refusal.named_floor === 'string' &&
      /anchor-discipline|configured anchor|different circuit/i.test(refusal.named_floor),
    refusal && refusal.named_floor ? refusal.named_floor.slice(0, 80) + '…' : 'no reason',
  );

  // (2b) The matching-anchor case: same fingerprint passes the discipline check
  // and reaches the (honestly reported) named byte-verify seam — NOT a false pass.
  const matched = await page.evaluate(async (base) => {
    const mod = await import(`${base}/playground/proving-client.js`);
    const client = new mod.ProvingClient();
    await client.ready();
    const fp = 'ab'.repeat(32);
    const envelope = JSON.stringify({
      version: 1,
      vk_fingerprint_hex: fp,
      proof_bytes_b64: '',
      genesis_root: 1,
      final_root: 2,
      chain_digest: 3,
      num_turns: 2,
    });
    return await client.verifyDevnetHistory(envelope, fp);
  }, BASE);
  check(
    'matching anchor passes discipline but does NOT fake-attest (byte seam named)',
    matched &&
      matched.attested === false &&
      /proof_bytes|byte-verify|serde|recursion-proof serialization/i.test(matched.named_floor || ''),
    matched && matched.named_floor ? matched.named_floor.slice(0, 80) + '…' : 'no reason',
  );

  // (3) The main thread is responsive while the worker holds a wasm instance: a
  // requestAnimationFrame tick lands within a generous frame budget.
  const rafMs = await page.evaluate(async (base) => {
    const mod = await import(`${base}/playground/proving-client.js`);
    const client = new mod.ProvingClient();
    await client.ready();
    const t0 = performance.now();
    await new Promise((r) => requestAnimationFrame(r));
    return performance.now() - t0;
  }, BASE);
  check('main thread stays responsive (rAF tick < 250ms with worker live)', rafMs < 250, `${rafMs.toFixed(1)}ms`);

  check('no uncaught page errors', pageErrors.length === 0, pageErrors.join(' | '));

  await browser.close();
  console.log(`\n${failures === 0 ? 'ALL PASS' : `${failures} FAILURE(S)`}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => {
  console.error('test harness error:', e);
  process.exit(2);
});
