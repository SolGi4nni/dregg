/**
 * Web-surface KILLER-DEMO end-to-end smoke test (N13 — the web evaluation
 * artifact): "TWO TABS, ONE SURFACE, the share that REFUSES".
 *
 * `docs/FRONTIER-ROADMAP.md §4` (the web killer demo) + `docs/WEB-FORWARD-EVERYWHERE.md`
 * (N13). The companion `web-surface-proving-worker.mjs` covers the off-thread
 * Worker + the `verify_history` anchor discipline; THIS test covers the SURFACE
 * demo state machine itself — the headline N13 deliverable — in a REAL headless
 * browser against the built dist, driving the REAL `dregg-cell`/`dregg-turn`
 * crates in wasm32 (NOT a mock):
 *
 *   1. Reachable from a URL — `/playground/#web-surface` activates the section.
 *   2. OPEN — `open_surface` returns a live T2 badge from the LEDGER (a 64-hex
 *      owning cell id + a 64-hex source-state-root), not a page claim.
 *   3. READ-ONLY SHARE — a real `GrantCapability` turn commits (`ok:true`); the
 *      recipient holds exactly `Signature` (the narrowed cap).
 *   4. THE OVER-SHARE REFUSAL (the climax) — an onward WRITABLE share REJECTS
 *      with the GENUINE `DelegationDenied` (no-amplification, `granted ⊄ held`)
 *      from the real executor — asserted on the executor's OWN reason, so it is
 *      the real refusal, NOT a faked banner; and the on-ledger state is unchanged
 *      (the recipient still holds only `Signature`, the widening produced no turn).
 *   5. REVOKE DARKENS — after `revoke_surface`, the cap is dead the instant it
 *      returns (`surface_holds_cap` false) and a subsequent `present_surface` is
 *      refused (the glass is dark this frame — n=1 synchronous).
 *   6. THE PIXEL LAYER — driving the demo through the UI (the "Run the next step"
 *      button), the `⚠ over-share` banner actually appears in the DOM at the
 *      refusal step, the compositor draws the T2 badge (`cell …`) from the ledger,
 *      and the two tabs both composite the SAME surface (same cell id).
 *   7. THE ANTI-PALE-GHOST TOOTH — the in-tab `verify_devnet_history` runs the
 *      REAL anchor-discipline check (config-not-artifact): a mismatched anchor is
 *      REFUSED, a matching one does NOT fake-attest (the byte-verify seam is named
 *      honestly). This is the instant verify tooth (no STARK proving); the full
 *      ~minutes fold (`light_client_demo`) is exercised by the Rust
 *      `dregg-lightclient` tests + manual playground use.
 *
 * Prereqs:  dist served (default http://localhost:8099)
 * Run:      PLAYGROUND_BASE=http://localhost:8099 node tests/web-surface-demo.mjs
 */

import { chromium } from '../node_modules/playwright/index.mjs';

const BASE = process.env.PLAYGROUND_BASE || 'http://localhost:8099';

let failures = 0;
function check(name, ok, detail = '') {
  console.log(`${ok ? 'PASS' : 'FAIL'}  ${name}${detail ? `  — ${detail}` : ''}`);
  if (!ok) failures += 1;
}

const HEX64 = /^[0-9a-f]{64}$/;

async function run() {
  const browser = await chromium.launch({ headless: true });
  const ctx = await browser.newContext();
  const page = await ctx.newPage();

  const pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));

  // (0) DISCOVERABLE: a stranger landing on the playground (default scenario)
  // finds the killer demo via the featured overview card — no tribal knowledge of
  // which scenario tab to click. Clicking it activates the demo + sets the
  // shareable #web-surface hash.
  await page.goto(`${BASE}/playground/`, { waitUntil: 'domcontentloaded' });
  await page
    .waitForFunction(
      () => document.getElementById('wasm-status')?.classList.contains('ready'),
      { timeout: 30000 },
    )
    .catch(() => {});
  const featureCard = page.locator('.overview-cap--feature[data-nav="web-surface"]');
  const featureVisible = (await featureCard.count()) === 1 && (await featureCard.isVisible());
  check('the killer demo is discoverable from the landing (featured overview card)', featureVisible);
  if (featureVisible) {
    await featureCard.click();
    await page.waitForTimeout(200);
    const wentVia = await page.evaluate(() =>
      document.getElementById('section-web-surface')?.classList.contains('active') === true &&
      location.hash === '#web-surface',
    );
    check('clicking the featured card activates the demo + sets the shareable #web-surface hash', wentVia);
  }

  // (1) Reachable from a URL: the hash activates the web-surface section.
  await page.goto(`${BASE}/playground/#web-surface`, { waitUntil: 'domcontentloaded' });
  await page
    .waitForFunction(
      () => document.getElementById('wasm-status')?.classList.contains('ready'),
      { timeout: 30000 },
    )
    .catch(() => {});
  const sectionActive = await page.evaluate(() =>
    document.getElementById('section-web-surface')?.classList.contains('active') === true,
  );
  check('URL #web-surface activates the killer-demo section', sectionActive);

  // The surface bindings must be present in THIS wasm build (the recursion-enabled
  // pkg). If they are absent the demo would silently degrade — fail loudly instead.
  const bindingsPresent = await page.evaluate(async () => {
    const mod = await import('../pkg/dregg_wasm.js');
    const need = [
      'create_runtime', 'create_agent', 'open_surface', 'share_surface',
      'present_surface', 'revoke_surface', 'surface_identity', 'surface_holds_cap',
      'surface_rights_held', 'destroy_runtime',
    ];
    return need.every((n) => typeof mod[n] === 'function');
  });
  check('the surface bindings ship in the served wasm (no silent degrade)', bindingsPresent);

  // (2)–(5) Drive the real bindings directly so the refusal is asserted on the
  // executor's OWN reason. This is the SAME wasm module + the SAME DreggRuntime
  // the section uses; we build a fresh world to keep the assertions hermetic.
  const machine = await page.evaluate(async () => {
    const wasm = await import('../pkg/dregg_wasm.js');
    const rt = wasm.create_runtime();
    try {
      const aliceIdx = wasm.create_agent(rt, 'alice', 30000n).agent_index ?? 0;
      const bobIdx = wasm.create_agent(rt, 'bob', 5000n).agent_index ?? 1;

      // OPEN — alice opens her cell as a WRITABLE surface (None = widest).
      const opened = wasm.open_surface(rt, aliceIdx, 'none');

      // READ-ONLY SHARE — a real GrantCapability turn, narrowed to Signature.
      const shareRO = wasm.share_surface(rt, aliceIdx, bobIdx, aliceIdx, 'signature');
      const bobHoldsAfterShare = wasm.surface_holds_cap(rt, bobIdx, aliceIdx);
      const bobRightsAfterShare = wasm.surface_rights_held(rt, bobIdx, aliceIdx);

      // THE OVER-SHARE — bob (holding Signature) tries to share ONWARD as None
      // (writable, wider). The executor must REJECT (DelegationDenied).
      const overShare = wasm.share_surface(rt, bobIdx, aliceIdx, aliceIdx, 'none');
      // ...and the on-ledger state must be unchanged — bob still holds ONLY
      // Signature, because the widening produced no committed turn.
      const bobRightsAfterOverShare = wasm.surface_rights_held(rt, bobIdx, aliceIdx);

      // REVOKE DARKENS — alice revokes bob's pane (synchronous at n=1).
      const revoked = wasm.revoke_surface(rt, bobIdx, aliceIdx);
      const bobHoldsAfterRevoke = wasm.surface_holds_cap(rt, bobIdx, aliceIdx);
      const presentAfterRevoke = wasm.present_surface(rt, bobIdx, aliceIdx, 'signature');

      return {
        opened, shareRO, bobHoldsAfterShare, bobRightsAfterShare,
        overShare, bobRightsAfterOverShare,
        revoked, bobHoldsAfterRevoke, presentAfterRevoke,
      };
    } finally {
      try { wasm.destroy_runtime(rt); } catch (_) {}
    }
  });

  // (2) OPEN — the badge is a live LEDGER read, not a page claim.
  check(
    'open_surface returns a live ledger T2 badge (64-hex cell id + state root)',
    machine.opened &&
      HEX64.test(machine.opened.owning_cell_id || '') &&
      HEX64.test(machine.opened.source_state_root || '') &&
      machine.opened.lifecycle === 'live' &&
      machine.opened.accepts_effects === true,
    `cell=${(machine.opened?.owning_cell_id || '').slice(0, 8)}… lifecycle=${machine.opened?.lifecycle}`,
  );

  // (3) READ-ONLY SHARE commits and the recipient holds exactly Signature.
  check(
    'read-only share commits as a real GrantCapability turn (ok:true)',
    machine.shareRO && machine.shareRO.ok === true,
    machine.shareRO?.reason?.slice(0, 70),
  );
  check(
    'recipient holds exactly the narrowed Signature cap after the share',
    machine.bobHoldsAfterShare === true && machine.bobRightsAfterShare === 'Signature',
    `holds=${machine.bobHoldsAfterShare} rights=${machine.bobRightsAfterShare}`,
  );

  // (4) THE OVER-SHARE REFUSAL — the genuine no-amplification denial.
  check(
    'the onward WRITABLE over-share is REFUSED (ok:false)',
    machine.overShare && machine.overShare.ok === false,
    machine.overShare?.reason?.slice(0, 90),
  );
  check(
    'the refusal is the GENUINE DelegationDenied / no-amplification (not a faked banner)',
    machine.overShare &&
      typeof machine.overShare.reason === 'string' &&
      /no-amplification denied/i.test(machine.overShare.reason) &&
      /delegation denied/i.test(machine.overShare.reason),
    machine.overShare?.reason?.slice(0, 90),
  );
  check(
    'no-amplification held: the recipient STILL holds only Signature (widening produced no turn)',
    machine.bobRightsAfterOverShare === 'Signature',
    `rights=${machine.bobRightsAfterOverShare}`,
  );

  // (5) REVOKE DARKENS the glass synchronously at n=1.
  check(
    'revoke removes the cap synchronously (dead the instant it returns)',
    machine.revoked === true && machine.bobHoldsAfterRevoke === false,
    `revoked=${machine.revoked} stillHolds=${machine.bobHoldsAfterRevoke}`,
  );
  check(
    'after revoke a present is refused — the glass is dark this frame (n=1)',
    machine.presentAfterRevoke && machine.presentAfterRevoke.ok === false,
    machine.presentAfterRevoke?.reason?.slice(0, 70),
  );

  // (6) THE PIXEL LAYER — drive the demo through the actual UI buttons and assert
  // the ⚠ over-share banner appears in the DOM at the refusal step, the compositor
  // draws the T2 badge from the ledger, and both tabs composite the SAME surface.
  const stepBtn = page.locator('#ws-step');
  await stepBtn.waitFor({ state: 'visible', timeout: 10000 });

  async function clickStep() {
    await stepBtn.click();
    // Let the synchronous turn + re-render settle.
    await page.waitForTimeout(120);
  }

  // reset() already ran on init (step 1 is "open"). Step through the machine.
  await clickStep(); // step 1: open alice's surface
  const aliceBadge = await page.evaluate(() => {
    const bar = document.querySelector('#ws-tab-alice .cmp-pane:not(.cmp-pane--console)');
    return bar ? bar.textContent : null;
  });
  check(
    'the compositor draws a cell-id badge (T2, from the ledger) on alice’s pane',
    typeof aliceBadge === 'string' && /cell\s+[0-9a-f]{4,}/i.test(aliceBadge),
    aliceBadge ? aliceBadge.replace(/\s+/g, ' ').slice(0, 60) : 'no pane',
  );

  await clickStep(); // step 2: share read-only with bob
  const sameSurface = await page.evaluate(() => {
    const head = (root) => {
      const pane = document.querySelector(`${root} .cmp-pane:not(.cmp-pane--console)`);
      const m = pane && pane.textContent.match(/cell\s+([0-9a-f]+)/i);
      return m ? m[1] : null;
    };
    return { alice: head('#ws-tab-alice'), bob: head('#ws-tab-bob') };
  });
  check(
    'both tabs composite the SAME surface (the shared pane shows alice’s cell id)',
    sameSurface.alice && sameSurface.bob && sameSurface.alice === sameSurface.bob,
    `alice=${sameSurface.alice} bob=${sameSurface.bob}`,
  );

  await clickStep(); // step 3: bob's onward over-share — REFUSED, ⚠ banner flashes
  const banner = await page.evaluate(() => {
    const el = document.getElementById('ws-banner');
    return el ? el.textContent : '';
  });
  check(
    'the ⚠ over-share banner fires at the pixel layer on the refusal step',
    /over-share/i.test(banner) && /⚠/.test(banner) &&
      /(DelegationDenied|granted)/i.test(banner),
    banner.replace(/\s+/g, ' ').slice(0, 90),
  );
  // The log must carry the REAL refusal line (warn), not a committed line.
  const logHasRefusal = await page.evaluate(() => {
    const log = document.getElementById('ws-log');
    return log ? /THE REFUSAL/i.test(log.textContent) && !/unexpectedly COMMITTED/i.test(log.textContent) : false;
  });
  check('the demo log records THE REFUSAL (and never a committed widening)', logHasRefusal === true);

  await clickStep(); // step 4: revoke — bob's pane darkens
  const bobPaneGone = await page.evaluate(() => {
    const pane = document.querySelector('#ws-tab-bob .cmp-pane:not(.cmp-pane--console)');
    return pane == null; // the shared pane is closed on revoke
  });
  check('revoking darks bob’s pane in the UI (the shared pane is closed)', bobPaneGone === true);

  // (7) THE ANTI-PALE-GHOST TOOTH — the in-tab verify discipline (instant path).
  const verify = await page.evaluate(async () => {
    const mod = await import('../pkg/dregg_wasm.js');
    // A mismatched config anchor must be REFUSED (anchor-discipline / config-not-
    // artifact); a matching one must NOT fake-attest (byte-verify seam is named).
    const mk = (fp) => JSON.stringify({
      version: 1, vk_fingerprint_hex: fp, proof_bytes_b64: '',
      genesis_root: 1, final_root: 2, chain_digest: 3, num_turns: 2,
    });
    const mismatched = mod.verify_devnet_history(mk('aa'.repeat(32)), 'cc'.repeat(32));
    const matched = mod.verify_devnet_history(mk('ab'.repeat(32)), 'ab'.repeat(32));
    return { mismatched, matched };
  });
  check(
    'verify_history (config-not-artifact): a mismatched anchor is REFUSED',
    verify.mismatched && verify.mismatched.attested === false &&
      /anchor-discipline|configured anchor|different circuit/i.test(verify.mismatched.named_floor || ''),
    verify.mismatched?.named_floor?.slice(0, 70),
  );
  check(
    'verify_history: a matching anchor does NOT fake-attest (byte seam named honestly)',
    verify.matched && verify.matched.attested === false &&
      /proof_bytes|byte-verify|serde|recursion-proof serialization/i.test(verify.matched.named_floor || ''),
    verify.matched?.named_floor?.slice(0, 70),
  );

  check('no uncaught page errors', pageErrors.length === 0, pageErrors.join(' | '));

  await browser.close();
  console.log(`\n${failures === 0 ? 'ALL PASS' : `${failures} FAILURE(S)`}`);
  process.exit(failures === 0 ? 0 : 1);
}

run().catch((e) => {
  console.error('test harness error:', e);
  process.exit(2);
});
