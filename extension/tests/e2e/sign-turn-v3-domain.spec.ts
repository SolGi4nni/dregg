/**
 * signTurnV3 federation-domain bridge — e2e over the REAL extension
 * (OWNER-LIFECYCLE-BROWSER-SEAM):
 *
 *   - `window.dregg.capabilities.signTurnV3FederationDomain` advertises the
 *     exact v1 string, frozen;
 *   - page-level typed rejection (wrong type / length 0/31/33 / fractional /
 *     negative / >255) BEFORE any permission or confirmation popup;
 *   - two-argument call: the confirmation popup renders the FULL 64-char
 *     lowercase hex of the domain that was signed;
 *   - one-argument call stays backward-compatible (zero domain, displayed);
 *   - the nonce-bound decision REFUSES a substituted domain echo;
 *   - a queued (node-down) submission retains the domain in outbox metadata.
 */
import { test, expect } from '../fixtures/extension';
import type { Page, BrowserContext } from '@playwright/test';
import { MockNode } from '../fixtures/node-mock';
import { readFileSync } from 'fs';
import path from 'path';

const EXT_ROOT = path.resolve(__dirname, '..', '..');
const CAPABILITY = 'dregg-sign-turn-v3-federation-domain/v1';

let mockNode: MockNode;

/**
 * Build a REAL Turn whose actions carry `Authorization::Unchecked` — the
 * shape dapp turn-builders hand `dregg.signTurnV3` — by driving the same
 * dregg wasm the extension ships, here in the Node test process.
 */
function buildUncheckedTurnBytes(): number[] {
  const glue = readFileSync(path.join(EXT_ROOT, 'dregg_wasm.js'), 'utf8');
  const wasmBytes = readFileSync(path.join(EXT_ROOT, 'dregg_wasm_bg.wasm'));
  // The glue is wasm-bindgen no-modules: evaluate it and take the initializer.
  const wb = new Function(`${glue}; return wasm_bindgen;`)() as any;
  wb.initSync({ module: wasmBytes });
  const kp = wb.derive_keypair_from_mnemonic(
    'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon ' +
    'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art',
    '', 'dregg/0');
  const sk = new Uint8Array(kp.secret_key);
  const built = wb.cipherclerk_make_action_turn(JSON.stringify({
    sender_privkey: Array.from(sk),
    method: 'propose_routes',
    memo_json: JSON.stringify({ routes: [] }),
  }));
  const signed = wb.sign_turn_v3(new Uint8Array(built.turn_bytes), sk, new Uint8Array(32));
  const turn = JSON.parse(Buffer.from(new Uint8Array(signed.turn_bytes_json)).toString('utf8'));
  for (const root of turn.call_forest.roots) root.action.authorization = 'Unchecked';
  return Array.from(Buffer.from(JSON.stringify(turn), 'utf8'));
}

const TURN_BYTES = buildUncheckedTurnBytes();

test.beforeAll(async () => {
  mockNode = new MockNode({ port: 8420 });
  await mockNode.start();
});

test.afterAll(async () => {
  await mockNode.stop();
});

test.beforeEach(async () => {
  mockNode.reset();
});

async function openDappPage(context: BrowserContext): Promise<Page> {
  const page = await context.newPage();
  await page.goto('https://example.com');
  await page.waitForFunction(() => 'dregg' in window, null, { timeout: 10000 });
  return page;
}

/**
 * Wait for an extension popup window whose URL contains `htmlName` —
 * including one that ALREADY opened before this call (windows.create popups
 * race the test's event registration).
 */
async function waitForPopup(context: BrowserContext, htmlName: string): Promise<Page> {
  const existing = context.pages().find((p) => p.url().includes(htmlName) && !p.isClosed());
  const popupPage = existing ?? await context.waitForEvent('page', {
    predicate: (p) => p.url().includes(htmlName),
    timeout: 15000,
  });
  await popupPage.waitForLoadState('domcontentloaded');
  return popupPage;
}

/**
 * Kick off `dregg.signTurnV3(turnBytes, federationId?)` in the dapp page
 * (returns immediately with a result promise handle stored on window), then
 * approve the origin-permission popup if one appears.
 */
async function startSignTurnV3(
  context: BrowserContext,
  page: Page,
  federationId: number[] | null,
): Promise<void> {
  await page.evaluate(([bytes, domain]) => {
    const w = window as any;
    w.__signResult = undefined;
    const args: unknown[] = [new Uint8Array(bytes as number[])];
    if (domain !== null) args.push(new Uint8Array(domain as number[]));
    (w.dregg.signTurnV3 as (...a: unknown[]) => Promise<unknown>)(...args)
      .then((r: unknown) => { w.__signResult = r; })
      .catch((e: Error) => { w.__signResult = { error: e.message, rejected: true }; });
  }, [TURN_BYTES, federationId] as const);

  // First restricted call from this origin raises the origin-permission
  // popup; approving persists the per-method grant. When the grant already
  // exists the confirm-intent popup opens directly instead.
  const first = await context.waitForEvent('page', {
    predicate: (p) => p.url().includes('origin-permission.html') || p.url().includes('confirm-intent.html'),
    timeout: 15000,
  });
  await first.waitForLoadState('domcontentloaded');
  if (first.url().includes('origin-permission.html')) {
    await first.click('#allowBtn');
  }
}

async function readSignResult(page: Page): Promise<any> {
  await page.waitForFunction(() => (window as any).__signResult !== undefined, null, { timeout: 15000 });
  return page.evaluate(() => (window as any).__signResult);
}

test.describe('capability advertisement', () => {
  test('window.dregg.capabilities advertises the federation-domain bridge, frozen', async ({ context }) => {
    const page = await openDappPage(context);
    const caps = await page.evaluate(() => {
      const d = (window as any).dregg;
      return {
        value: d.capabilities?.signTurnV3FederationDomain,
        frozen: Object.isFrozen(d.capabilities),
        mutationSticks: (() => {
          try { d.capabilities.signTurnV3FederationDomain = 'evil'; } catch (_e) { /* strict-mode throw */ }
          return d.capabilities.signTurnV3FederationDomain !== 'evil';
        })(),
      };
    });
    expect(caps.value).toBe(CAPABILITY);
    expect(caps.frozen).toBe(true);
    expect(caps.mutationSticks).toBe(true);
    await page.close();
  });
});

test.describe('page-level typed rejection (before any popup or signing)', () => {
  test('invalid domains reject in the page; no permission/confirmation popup opens', async ({ context }) => {
    const page = await openDappPage(context);
    const popupsSeen: string[] = [];
    context.on('page', (p) => popupsSeen.push(p.url()));

    const cases: Array<[string, unknown]> = [
      ['length 0', []],
      ['length 31', new Array(31).fill(0)],
      ['length 33', new Array(33).fill(0)],
      ['fractional element', (() => { const a = new Array(32).fill(0); a[5] = 1.5; return a; })()],
      ['negative element', (() => { const a = new Array(32).fill(0); a[5] = -1; return a; })()],
      ['element > 255', (() => { const a = new Array(32).fill(0); a[5] = 256; return a; })()],
      ['wrong type: string', 'ff'.repeat(32)],
      ['wrong type: object', { length: 32 }],
    ];
    for (const [label, bad] of cases) {
      const result = await page.evaluate(async ([bytes, domain]) => {
        try {
          // Plain arrays are accepted by the validator shape-wise, so these
          // exercise the element checks; non-arrays exercise the type check.
          await (window as any).dregg.signTurnV3(new Uint8Array(bytes as number[]), domain);
          return { rejected: false };
        } catch (e: any) {
          return { rejected: true, name: e.constructor.name, message: String(e.message) };
        }
      }, [TURN_BYTES, bad] as const);
      expect(result.rejected, `${label} rejected`).toBe(true);
      expect(result.name, `${label} is a TypeError`).toBe('TypeError');
      expect(result.message).toContain('dregg.signTurnV3');
    }

    // Typed rejection happened BEFORE dispatch: no popup of any kind opened.
    await page.waitForTimeout(500);
    expect(popupsSeen.filter((u) => u.includes('origin-permission') || u.includes('confirm-intent'))).toEqual([]);
    await page.close();
  });
});

test.describe('federation domain through the full bridge', () => {
  test('nonzero domain: popup shows all 64 lowercase hex chars; accept submits', async ({ context }) => {
    const page = await openDappPage(context);
    const domain = new Array(32).fill(0).map((_, i) => (i * 7 + 3) % 256);
    const domainHex = domain.map((b) => b.toString(16).padStart(2, '0')).join('');

    await startSignTurnV3(context, page, domain);
    const confirm = await waitForPopup(context, 'confirm-intent.html');

    // The FULL domain that was signed, rendered as its own detail row.
    await expect(confirm.locator('#federationRow')).toBeVisible();
    await expect(confirm.locator('#federationDomain')).toHaveText(domainHex);
    expect(domainHex).toMatch(/^[0-9a-f]{64}$/);

    await confirm.click('#acceptBtn');
    const result = await readSignResult(page);
    expect(result.rejected).toBeUndefined();
    expect(result.submitted).toBe(true);
    expect(mockNode.state.lastSubmittedTurn).toBeTruthy();
    await page.close();
  });

  test('one-argument call stays backward-compatible: signs and displays the zero domain', async ({ context }) => {
    const page = await openDappPage(context);
    await startSignTurnV3(context, page, null);
    const confirm = await waitForPopup(context, 'confirm-intent.html');

    await expect(confirm.locator('#federationDomain')).toHaveText('0'.repeat(64));
    await confirm.click('#acceptBtn');
    const result = await readSignResult(page);
    expect(result.submitted).toBe(true);
    await page.close();
  });

  test('nonce-bound decision refuses a substituted domain echo', async ({ context }) => {
    const page = await openDappPage(context);
    const domain = new Array(32).fill(0xab);

    await startSignTurnV3(context, page, domain);
    const confirm = await waitForPopup(context, 'confirm-intent.html');

    // Forge an ACCEPT from the genuine popup window (valid sender + valid
    // nonce) but with a substituted domain echo. The background must treat
    // it as a decline — consent is only consent for exactly what was shown.
    const displayedTurnId = await confirm.evaluate(async () => {
      const nonce = (window.location.hash.match(/nonce=([0-9a-f]+)/) || [])[1];
      const resp = await (window as any).chrome.runtime.sendMessage({
        type: 'dregg:getPendingDecision', nonce,
      });
      return resp?.result?.payload?.turnId as string;
    });
    await confirm.evaluate(async (turnId) => {
      const nonce = (window.location.hash.match(/nonce=([0-9a-f]+)/) || [])[1];
      await (window as any).chrome.runtime.sendMessage({
        type: 'dregg:intentConfirmation',
        nonce,
        confirmed: true,
        turnId,
        federationDomainHex: 'ff'.repeat(32), // NOT what was displayed/signed
      });
    }, displayedTurnId);

    const result = await readSignResult(page);
    expect(result.submitted).toBe(false);
    expect(String(result.error)).toContain('declined');
    expect(mockNode.state.lastSubmittedTurn).toBeNull();
    await confirm.close().catch(() => {});
    await page.close();
  });

  test('node-down submission queues with the domain retained in outbox metadata', async ({ context, popup }) => {
    const page = await openDappPage(context);
    const domain = new Array(32).fill(0).map((_, i) => 255 - i);
    const domainHex = domain.map((b) => b.toString(16).padStart(2, '0')).join('');

    await mockNode.stop(); // unreachable node → durable outbox queueing
    try {
      await startSignTurnV3(context, page, domain);
      const confirm = await waitForPopup(context, 'confirm-intent.html');
      await expect(confirm.locator('#federationDomain')).toHaveText(domainHex);
      await confirm.click('#acceptBtn');

      const result = await readSignResult(page);
      expect(result.submitted).toBe(false);
      expect(result.queued).toBe(true);
    } finally {
      await mockNode.start();
    }

    // The outbox entry carries the selected domain in metadata — a retry can
    // never silently fall back to zero. Read it via the extension's own
    // popup page (popup-only surface reads storage through the background).
    const entries = await popup.evaluate(async () => {
      const stored = await (window as any).chrome.storage.local.get('dregg_extension_outbox');
      return stored['dregg_extension_outbox'] || [];
    });
    const mine = entries.filter((e: any) => e?.metadata?.action === 'signTurnV3');
    expect(mine.length).toBeGreaterThan(0);
    expect(mine[mine.length - 1].metadata.federationDomainHex).toBe(domainHex);
    await page.close();
  });
});
