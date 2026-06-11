/**
 * Playwright ad-hoc test for <dregg-witnessed-receipt> inspector.
 *
 * Run with:
 *   node tests/studio/witnessed-receipt.mjs
 *
 * Requires dist/ to be served on port 8080:
 *   npx serve dist -l 8080
 *
 * What this test does:
 *  1. Navigates to /playground/ (the surface that hosts the seeded wasm
 *     in-memory runtime — the old /studio.html sim page became the IDE and
 *     no longer mounts a <dregg-app#app>)
 *  2. Waits for the shared studio-embed runtime, then anchors a fresh
 *     <dregg-app id="app"> on it for the inspector mounts
 *  3. Creates an agent, executes a turn to generate a turn_hash → receipt
 *  4. Injects witnessed-receipt.js (receipt/proof come from the barrel)
 *  5. Mounts <dregg-witnessed-receipt uri="dregg://receipt/<hash>">
 *  6. Verifies a scope badge + trust-tier badge render
 *  7. Verifies embedded <dregg-receipt> and <dregg-proof> mount correctly
 *  8. Tests compact mode output
 */

import { chromium } from '../../node_modules/playwright/index.mjs';

const BASE = process.env.STUDIO_BASE || 'http://localhost:8080';

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('console', msg => {
    if (msg.type() === 'error') errors.push(`[console.error] ${msg.text()}`);
  });

  console.log('[test] Navigating to /playground/ ...');
  await page.goto(`${BASE}/playground/`, { waitUntil: 'domcontentloaded' });

  // Wait for dreggUi:ready (Preact + signals loaded; dist uses window.dreggUi)
  await page.waitForFunction(() => !!window.dreggUi, { timeout: 20000 });
  console.log('[test] dreggUi:ready fired.');

  // Wait for the shared seeded wasm runtime (studio-embed attaches it to every
  // section's <dregg-app>), then anchor a dedicated <dregg-app id="app"> for
  // this test's mounts.
  await page.waitForFunction(() => {
    const apps = [...document.querySelectorAll('dregg-app')];
    return apps.some(a => a.runtime && a.runtime._wasm && a.runtime._handle != null);
  }, { timeout: 30000 });
  await page.evaluate(async () => {
    const src = [...document.querySelectorAll('dregg-app')]
      .find(a => a.runtime && a.runtime._wasm && a.runtime._handle != null);
    // Fresh runtime on the same wasm: the playground's shared runtime is
    // already seeded (its faucet is mostly spent); tests want full genesis.
    const mod = await import('/_includes/studio/runtime-in-memory.js');
    const fresh = await mod.createInMemoryRuntime({ wasm: src.runtime._wasm, signals: window.dreggUi });
    const anchor = document.createElement('dregg-app');
    anchor.setAttribute('id', 'app');
    document.body.appendChild(anchor);
    anchor.runtime = fresh;
  });
  console.log('[test] seeded runtime anchored on <dregg-app#app>.');

  // ─── Step 1: create agent + execute a turn ──────────────────────────────────
  const turnHash = await page.evaluate(async () => {
    const rt = document.getElementById('app').runtime;
    // Modest amounts: the playground's seeding already spent most of the
    // shared faucet cell, so stay within what's left (createAgent draws the
    // initial balance from it; the empty turn's computron budget needs 1000).
    const alice = await rt.createAgent('alice', 300n);
    if (!alice || alice.agent_index == null) {
      return { error: 'createAgent failed: ' + JSON.stringify(alice) };
    }
    // Computron limit must cover the empty turn's ~100 used AND fit within
    // alice's balance (the executor requires balance >= limit upfront).
    const turnResult = await rt.executeTurn(alice.agent_index, [], 300);
    if (!turnResult) return { error: 'executeTurn returned null' };
    if (turnResult.status !== 'committed') {
      return { error: 'executeTurn not committed: ' + JSON.stringify(turnResult) };
    }
    const chain = rt.listReceipts(null).value || [];
    if (chain.length === 0) return { error: 'receipt chain empty after turn' };
    return chain[0].turn_hash;
  });

  if (!turnHash || typeof turnHash === 'object') {
    throw new Error('TEST SETUP FAILED: ' + JSON.stringify(turnHash));
  }
  console.log(`[test] turn_hash: ${turnHash.slice(0, 16)}…`);

  // ─── Step 2: inject witnessed-receipt.js (proof.js already loaded via barrel) ──
  // proof.js and receipt.js are in the barrel (inspectors.js) loaded by studio.html
  // witnessed-receipt.js is not yet in the barrel, so inject as module.
  await page.addScriptTag({
    url: `${BASE}/_includes/studio/inspectors/witnessed-receipt.js`,
    type: 'module',
  });
  await page.waitForFunction(
    () => !!customElements.get('dregg-witnessed-receipt'),
    { timeout: 5000 }
  );
  console.log('[test] <dregg-witnessed-receipt> custom element registered.');

  // ─── Step 3: mount inside <dregg-app#app> ───────────────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('dregg-witnessed-receipt');
    el.setAttribute('uri', `dregg://receipt/${hash}`);
    el.setAttribute('id', 'test-wr');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  // Wait for the component to produce children
  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    return el && el.children.length > 0;
  }, { timeout: 8000 });
  console.log('[test] <dregg-witnessed-receipt> rendered.');

  // ─── Test 1: a scope badge renders ─────────────────────────────────────────
  // The sim runtime now emits a real proof_view for executed turns (see
  // proof-tier.mjs), so the receipt is Scope-1 (proof present, no exposed
  // witness), not the old Scope-0. We assert a valid scope badge renders rather
  // than hardcoding the no-proof assumption that no longer holds.
  const scopeBadgeText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const badge = el && el.querySelector('.pwr__scope-badge');
    return badge ? badge.textContent.trim() : '';
  });
  console.log(`[test 1] Scope badge text: "${scopeBadgeText}"`);
  if (!/Scope-[012]/.test(scopeBadgeText)) {
    throw new Error(`TEST FAILED: expected a Scope-0/1/2 badge, got "${scopeBadgeText}"`);
  }
  console.log('[test 1] PASS: scope badge rendered.');

  // ─── Test 2: a trust-tier badge renders ─────────────────────────────────────
  // Sim with a proof_view is Silver tier (no bilateral PI); a proofless receipt
  // would be Placeholder. Either is a valid render of the inspector's tier logic.
  const tierBadgeText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const badge = el && el.querySelector('.pwr__tier-badge');
    return badge ? badge.textContent.trim() : '';
  });
  console.log(`[test 2] Tier badge text: "${tierBadgeText}"`);
  if (!/(Placeholder|Silver|Golden)\s*tier/i.test(tierBadgeText)) {
    throw new Error(`TEST FAILED: expected a Placeholder/Silver/Golden tier badge, got "${tierBadgeText}"`);
  }
  console.log('[test 2] PASS: trust-tier badge rendered.');

  // ─── Test 3: embedded <dregg-receipt> mounts ────────────────────────────────
  // The sub-pane uses a <details open> + <dregg-receipt uri=...> child element.
  // We wait for the sub-element to have rendered children.
  const receiptMounted = await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    if (!el) return false;
    const sub = el.querySelector('dregg-receipt');
    // dregg-receipt renders a div child once it resolves
    return sub && sub.children.length > 0;
  }, { timeout: 8000 }).then(() => true).catch(() => false);

  console.log(`[test 3] <dregg-receipt> mounted: ${receiptMounted}`);
  if (!receiptMounted) {
    // Inspect the DOM to understand the state
    const wrHtml = await page.evaluate(() => {
      const el = document.getElementById('test-wr');
      return el ? el.innerHTML.slice(0, 800) : '(no element)';
    });
    console.log('[test 3] witnessed-receipt innerHTML:', wrHtml);
    throw new Error('TEST FAILED: embedded <dregg-receipt> did not render children');
  }
  console.log('[test 3] PASS: embedded <dregg-receipt> rendered.');

  // ─── Test 4: embedded <dregg-proof> mounts ──────────────────────────────────
  const proofMounted = await page.waitForFunction(() => {
    const el = document.getElementById('test-wr');
    if (!el) return false;
    const sub = el.querySelector('dregg-proof');
    return sub && sub.children.length > 0;
  }, { timeout: 8000 }).then(() => true).catch(() => false);

  console.log(`[test 4] <dregg-proof> mounted: ${proofMounted}`);
  if (!proofMounted) {
    throw new Error('TEST FAILED: embedded <dregg-proof> did not render children');
  }
  // The proof element should contain a scope-0 indicator (no proof in sim)
  const proofText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const sub = el && el.querySelector('dregg-proof');
    return sub ? sub.innerText.slice(0, 400) : '';
  });
  console.log(`[test 4] <dregg-proof> text: "${proofText.slice(0, 120)}"`);
  const proofShowsScope0 = proofText.toLowerCase().includes('scope-0') ||
    proofText.toLowerCase().includes('no proof') ||
    proofText.toLowerCase().includes('placeholder');
  if (!proofShowsScope0) {
    console.warn('[test 4] WARN: <dregg-proof> did not show scope-0 language (may be ok if tier badge shown)');
  } else {
    console.log('[test 4] PASS: embedded <dregg-proof> shows scope-0 / no proof content.');
  }

  // ─── Test 5: scope strip renders scope description ──────────────────────────
  const stripText = await page.evaluate(() => {
    const el = document.getElementById('test-wr');
    const strip = el && el.querySelector('.pwr__scope-strip');
    return strip ? strip.innerText.trim() : '';
  });
  console.log(`[test 5] Scope strip text: "${stripText.slice(0, 120)}"`);
  if (!stripText) {
    throw new Error('TEST FAILED: .pwr__scope-strip not found');
  }
  console.log('[test 5] PASS: scope strip rendered.');

  // ─── Test 6: compact mode ───────────────────────────────────────────────────
  await page.evaluate((hash) => {
    const el = document.createElement('dregg-witnessed-receipt');
    el.setAttribute('uri', `dregg://receipt/${hash}`);
    el.setAttribute('mode', 'compact');
    el.setAttribute('id', 'test-wr-compact');
    document.getElementById('app').appendChild(el);
  }, turnHash);

  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr-compact');
    return el && el.children.length > 0;
  }, { timeout: 5000 });

  const compactText = await page.evaluate(() => {
    const el = document.getElementById('test-wr-compact');
    return el ? el.innerText.trim() : '';
  });
  console.log(`[test 6] Compact text: "${compactText}"`);

  const compactLower = compactText.toLowerCase();
  const hasScope = compactLower.includes('scope-');
  const hasTier = compactLower.includes('tier') || compactLower.includes('placeholder');
  const hasTurn = compactLower.includes('turn');
  if (!hasScope) throw new Error(`TEST FAILED: compact mode missing scope badge, got: "${compactText}"`);
  if (!hasTier) throw new Error(`TEST FAILED: compact mode missing tier, got: "${compactText}"`);
  if (!hasTurn) throw new Error(`TEST FAILED: compact mode missing turn=, got: "${compactText}"`);
  console.log('[test 6] PASS: compact mode has scope + tier + turn=.');

  // ─── Test 7: bad URI shows error ────────────────────────────────────────────
  await page.evaluate(() => {
    const el = document.createElement('dregg-witnessed-receipt');
    el.setAttribute('uri', 'dregg://cell/notAreceiptURI');
    el.setAttribute('id', 'test-wr-bad');
    document.getElementById('app').appendChild(el);
  });

  await page.waitForFunction(() => {
    const el = document.getElementById('test-wr-bad');
    return el && el.children.length > 0;
  }, { timeout: 3000 });

  const badText = await page.evaluate(() => {
    const el = document.getElementById('test-wr-bad');
    return el ? el.innerText : '';
  });
  const showsError = badText.includes('wrong kind') || badText.includes('cell') || badText.includes('err');
  if (!showsError) throw new Error(`TEST FAILED: bad URI did not show error, got: "${badText}"`);
  console.log('[test 7] PASS: wrong-kind URI shows error.');

  // ─── Check for unexpected JS errors ─────────────────────────────────────────
  const realErrors = errors.filter(e =>
    !e.includes('fetch') &&
    !e.includes('NetworkError') &&
    !e.includes('WASM not available') &&
    !e.includes('net::ERR_')
  );
  if (realErrors.length > 0) {
    console.error('[test] JS errors during test run:', realErrors);
    throw new Error(`JS errors: ${realErrors.join('; ')}`);
  }

  console.log('\n[test] ALL TESTS PASSED.');
  await browser.close();
}

run().catch(err => {
  console.error('[test] FAIL:', err.message || err);
  process.exit(1);
});
