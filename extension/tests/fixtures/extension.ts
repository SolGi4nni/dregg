import { test as base, chromium, type BrowserContext, type Page } from '@playwright/test';
import path from 'path';

export type ExtensionFixtures = {
  context: BrowserContext;
  extensionId: string;
  popup: Page;
  backgroundPage: { url: string };
};

export const test = base.extend<ExtensionFixtures>({
  // Launch a persistent context with the extension loaded.
  //
  // HEADLESS: Playwright's default `headless: true` uses the headless-shell
  // binary, which does NOT support extensions (the source of the old
  // "extensions require headed mode" rule). The FULL Chromium binary
  // (`channel: 'chromium'`) in new-headless mode loads MV3 extensions fine —
  // service worker, content scripts, and chrome.windows.create popups all
  // work — with no window flashing and a faster launch. Set HEADED=1 to
  // debug with visible windows.
  context: async ({}, use) => {
    const pathToExtension = path.resolve(__dirname, '..', '..');
    const context = await chromium.launchPersistentContext('', {
      channel: 'chromium',
      headless: !process.env.HEADED,
      args: [
        `--disable-extensions-except=${pathToExtension}`,
        `--load-extension=${pathToExtension}`,
        '--no-first-run',
        // NOTE: no --disable-gpu — in new-headless it forces software GL,
        // which multiplied per-test time ~4x on macOS.
      ],
    });
    await use(context);
    await context.close();
  },

  // Extract the extension ID from the service worker URL.
  extensionId: async ({ context }, use) => {
    let [background] = context.serviceWorkers();
    if (!background) {
      background = await context.waitForEvent('serviceworker');
    }
    const extensionId = background.url().split('/')[2];
    await use(extensionId);
  },

  // Open the popup page directly by navigating to its chrome-extension:// URL.
  // Before handing the popup to the test, point the extension's node config
  // at the hermetic MockNode (localhost:8420) so tests never depend on (or
  // vacuously "pass" against) the public devnet gateway. This drives the real
  // settings page UI: chrome.runtime.sendMessage initiated from a Playwright
  // evaluate() hangs in extension pages, but the page script's own handler
  // for a (trusted) click works.
  popup: async ({ context, extensionId }, use) => {
    const settings = await context.newPage();
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

    const popupUrl = `chrome-extension://${extensionId}/popup.html`;
    const page = await context.newPage();
    await page.goto(popupUrl);
    await page.waitForLoadState('domcontentloaded');
    // A fresh install now starts UNINITIALIZED (no auto-created wallet — MF-1).
    // Run the real onboarding flow once so the wallet exists + is unlocked for
    // the test. Idempotent: skips if a wallet already exists.
    await ensureOnboarded(page);
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

/** The passphrase the e2e onboarding sets (and unlockPopup re-types). */
export const E2E_PASSPHRASE = 'e2e-passphrase';

/**
 * Run first-run onboarding through the real popup UI if the wallet is
 * uninitialized: set a passphrase, read the displayed recovery phrase, confirm
 * it, and create the wallet (which leaves it unlocked). Idempotent — returns
 * immediately if a wallet already exists (onboarding section hidden).
 */
export async function ensureOnboarded(popup: Page): Promise<void> {
  const onboarding = popup.locator('#onboardingSection');
  // Let the initial refresh() decide visibility.
  await popup.waitForTimeout(300);
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
 * Unlock the cipherclerk through the popup's real unlock flow. After onboarding
 * the wallet is already unlocked, so this no-ops unless a test locked it.
 */
export async function unlockPopup(popup: Page): Promise<void> {
  await ensureOnboarded(popup);
  const lockBtn = popup.locator('#lockBtn');
  // The button's static HTML text is "Lock Cipherclerk"; the initial
  // refresh() flips it to "Unlock Cipherclerk" for the locked-at-rest clerk.
  // Wait for that refresh to land before deciding (the passphrase section is
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
