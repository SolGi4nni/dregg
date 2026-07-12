import { test as base, chromium, type BrowserContext, type Page } from '@playwright/test';
import path from 'path';

/**
 * Extension e2e fixtures — WORKER-SCOPED browser, per-test state reset.
 *
 * The old fixtures launched a fresh persistent context and re-ran the full
 * settings + onboarding flow for EVERY test (~3-4s of pure setup × ~70 tests,
 * serial). Now:
 *
 *   - `context` / `extensionId` are worker-scoped: ONE headless Chromium with
 *     the extension loaded serves every spec file in the worker.
 *   - `workerWallet` (worker-scoped) configures the MockNode endpoint and runs
 *     REAL onboarding exactly once, then captures a pristine snapshot of
 *     chrome.storage.local (encrypted wallet + node config).
 *   - `resetState` (auto, per test) restores that snapshot, drops live refs
 *     through the real popup-only API, and lock/unlock-cycles the clerk so the
 *     background's in-memory state (decrypted wallet, auth log, tokens) is
 *     rebuilt from the pristine snapshot. Every test starts from the same
 *     freshly-onboarded, unlocked, empty-allowlist world — without paying for
 *     a browser launch or an onboarding flow.
 *
 * HEADLESS: Playwright's default `headless: true` uses the headless-shell
 * binary, which does NOT support extensions (the source of the old
 * "extensions require headed mode" rule). The FULL Chromium binary
 * (`channel: 'chromium'`) in new-headless mode loads MV3 extensions fine —
 * service worker, content scripts, and chrome.windows.create popups all
 * work — with no window flashing. Do NOT pass --disable-gpu: in new headless
 * it forces software GL, which multiplied per-test time ~4x on macOS.
 * Set HEADED=1 to debug with visible windows.
 */

export type ExtensionFixtures = {
  context: BrowserContext;
  popup: Page;
  backgroundPage: { url: string };
  /** Auto fixture: pristine wallet + empty volatile state before every test. */
  resetState: void;
};

export type ExtensionWorkerFixtures = {
  /** Worker-scoped persistent context (the builtin `context` name is
   *  test-scoped in Playwright and cannot be redefined at worker scope;
   *  the test-scoped `context` below passes this through). */
  extContext: BrowserContext;
  extensionId: string;
  workerWallet: { janitor: Page; snapshot: Record<string, unknown> };
};

/** The passphrase the e2e onboarding sets (and unlockPopup re-types). */
export const E2E_PASSPHRASE = 'e2e-passphrase';

export const test = base.extend<ExtensionFixtures, ExtensionWorkerFixtures>({
  // ONE persistent context with the extension loaded, per worker.
  extContext: [async ({}, use) => {
    const pathToExtension = path.resolve(__dirname, '..', '..');
    const context = await chromium.launchPersistentContext('', {
      channel: 'chromium',
      headless: !process.env.HEADED,
      args: [
        `--disable-extensions-except=${pathToExtension}`,
        `--load-extension=${pathToExtension}`,
        '--no-first-run',
      ],
    });
    await use(context);
    await context.close();
  }, { scope: 'worker' }],

  // Every test's `context` is the worker's shared persistent context.
  context: async ({ extContext }, use) => {
    await use(extContext);
  },

  // Extract the extension ID from the service worker URL.
  extensionId: [async ({ extContext }, use) => {
    let [background] = extContext.serviceWorkers();
    if (!background) {
      background = await extContext.waitForEvent('serviceworker');
    }
    const extensionId = background.url().split('/')[2];
    await use(extensionId);
  }, { scope: 'worker' }],

  // One-time (per worker): point the extension at the hermetic MockNode via
  // the real settings UI, run REAL first-run onboarding via the real popup
  // UI, snapshot the resulting storage, and keep a "janitor" extension page
  // open for per-test resets (extension pages can call popup-only messages).
  workerWallet: [async ({ extContext, extensionId }, use) => {
    const settings = await extContext.newPage();
    settings.on('dialog', (d) => void d.accept()); // host-change confirm
    await settings.goto(`chrome-extension://${extensionId}/settings.html`);
    await settings.waitForLoadState('domcontentloaded');
    await settings.fill('#nodeUrl', 'http://localhost:8420');
    await settings.fill('#wssUrl', 'ws://localhost:8420/ws');
    await settings.fill('#wsUrl', 'ws://localhost:8420/ws');
    await settings.fill('#devnetKey', '');
    await settings.click('#saveBtn');
    await settings.waitForFunction(() =>
      /saved/i.test(document.getElementById('statusMsg')?.textContent || ''));
    await settings.close();

    const popupPage = await extContext.newPage();
    await popupPage.goto(`chrome-extension://${extensionId}/popup.html`);
    await popupPage.waitForLoadState('domcontentloaded');
    await ensureOnboarded(popupPage);
    await popupPage.close();

    // Janitor page: any extension page qualifies as a popup-only sender.
    const janitor = await extContext.newPage();
    await janitor.goto(`chrome-extension://${extensionId}/settings.html`);
    await janitor.waitForLoadState('domcontentloaded');
    const snapshot = await janitor.evaluate(async () =>
      await chrome.storage.local.get(null) as Record<string, unknown>);

    await use({ janitor, snapshot });
    await janitor.close();
  }, { scope: 'worker' }],

  // Per-test reset (auto): every test starts freshly-onboarded + unlocked,
  // with an empty allowlist/outbox/log and no live refs. Order matters:
  // everything that WRITES storage happens BEFORE the snapshot restore —
  // `dregg:lock` persists the dirty in-memory wallet (incl. the auth log)
  // and dropLiveRef persists the live-ref map — and `dregg:unlock` comes
  // LAST because it rebuilds the background's entire in-memory state from
  // the (now pristine) encrypted envelope in storage.
  resetState: [async ({ workerWallet }, use) => {
    const { janitor, snapshot } = workerWallet;
    await janitor.evaluate(async (snap) => {
      const send = (msg: Record<string, unknown>): Promise<Record<string, unknown> | undefined> =>
        chrome.runtime.sendMessage({ id: 'e2e-reset', ...msg });
      const refsResp = (await send({ type: 'dregg:getLiveRefs' })) as
        { result?: Array<{ refId: string }> | { refs?: Array<{ refId: string }> } } | undefined;
      const refs = Array.isArray(refsResp?.result)
        ? refsResp.result
        : ((refsResp?.result as { refs?: Array<{ refId: string }> })?.refs ?? []);
      for (const r of refs) {
        await send({ type: 'dregg:dropLiveRef', refId: r.refId });
      }
      await send({ type: 'dregg:lock' });
      await chrome.storage.local.clear();
      await chrome.storage.local.set(snap);
      const unlocked = (await send({ type: 'dregg:unlock', passphrase: 'e2e-passphrase' })) as
        { result?: { success?: boolean } } | undefined;
      if (unlocked?.result?.success !== true) {
        throw new Error(`e2e resetState: unlock failed: ${JSON.stringify(unlocked)}`);
      }
    }, snapshot);
    await use();
  }, { auto: true }],

  // A fresh popup page per test (the worker-scoped reset guarantees it opens
  // onto an onboarded, unlocked wallet).
  popup: async ({ context, extensionId, resetState }, use) => {
    void resetState;
    const page = await context.newPage();
    await page.goto(`chrome-extension://${extensionId}/popup.html`);
    await page.waitForLoadState('domcontentloaded');
    await use(page);
    await page.close();
  },

  // Expose background service worker info.
  backgroundPage: async ({ context }, use) => {
    let [background] = context.serviceWorkers();
    if (!background) {
      background = await context.waitForEvent('serviceworker');
    }
    await use({ url: background.url() });
  },
});

export { expect } from '@playwright/test';

/**
 * Run first-run onboarding through the real popup UI if the wallet is
 * uninitialized: set a passphrase, read the displayed recovery phrase, confirm
 * it, and create the wallet (which leaves it unlocked). Idempotent — returns
 * immediately if a wallet already exists (onboarding section hidden).
 */
export async function ensureOnboarded(popup: Page): Promise<void> {
  // Wait for the initial refresh() to decide state: it un-hides exactly one
  // of onboarding (uninitialized), the passphrase section (locked), or the
  // backup button (unlocked). Deterministic — no fixed sleep.
  await popup.waitForFunction(() => {
    const ob = document.getElementById('onboardingSection');
    const pass = document.getElementById('passphraseSection');
    const backup = document.getElementById('backupBtn');
    return (ob && !ob.classList.contains('hidden')) ||
      (pass && !pass.classList.contains('hidden')) ||
      (backup && backup.style.display === 'block');
  }, null, { timeout: 10000 });
  const onboarding = popup.locator('#onboardingSection');
  if (!(await onboarding.isVisible())) return;

  await popup.fill('#onbPass', E2E_PASSPHRASE);
  await popup.fill('#onbPassConfirm', E2E_PASSPHRASE);
  await popup.click('#onbNextBtn');
  await popup.locator('#onbStep2:not(.hidden)').waitFor({ state: 'attached', timeout: 5000 });

  // The phrase renders as "01. word  02. word ..."; strip the "NN. " prefixes.
  const words = await popup.locator('#onbMnemonic').evaluate((el) =>
    (el.textContent || '')
      .split(/\s+/)
      .filter((t) => t && !/^\d+\.?$/.test(t))
      .join(' '));
  await popup.fill('#onbConfirm', words);
  await popup.click('#onbCreateBtn');
  await onboarding.waitFor({ state: 'hidden', timeout: 5000 });
}

/**
 * Unlock the cipherclerk through the popup's real unlock flow. The reset
 * fixture leaves the wallet unlocked, so this no-ops unless a test locked it.
 */
export async function unlockPopup(popup: Page): Promise<void> {
  await ensureOnboarded(popup);
  const lockBtn = popup.locator('#lockBtn');
  // The button's static HTML text is "Lock Cipherclerk"; the initial
  // refresh() flips it to "Unlock Cipherclerk" for a locked clerk. Wait for
  // that refresh to land before deciding (the passphrase section is
  // unhidden in the same render).
  await popup.locator('#passphraseSection:not(.hidden), #backupBtn[style*="block"]')
    .first().waitFor({ state: 'attached', timeout: 5000 });
  if ((await lockBtn.textContent())?.includes('Unlock')) {
    await popup.fill('#passphraseInput', E2E_PASSPHRASE);
    await lockBtn.click();
    // Exact comparison: hasText would substring-match "Unlock Cipherclerk".
    await popup.waitForFunction(
      () => document.getElementById('lockBtn')?.textContent === 'Lock Cipherclerk',
      null,
      { timeout: 5000 },
    );
  }
}
