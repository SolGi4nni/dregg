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
  context: async ({}, use) => {
    const pathToExtension = path.resolve(__dirname, '..', '..');
    const context = await chromium.launchPersistentContext('', {
      headless: false,
      args: [
        `--disable-extensions-except=${pathToExtension}`,
        `--load-extension=${pathToExtension}`,
        '--no-first-run',
        '--disable-gpu',
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
 * Unlock the cipherclerk through the popup's real unlock flow. Before a user
 * passphrase is set (needsPassphraseSetup), the background falls back to the
 * installation's internal key, so any typed passphrase unlocks.
 */
export async function unlockPopup(popup: Page): Promise<void> {
  const lockBtn = popup.locator('#lockBtn');
  // The button's static HTML text is "Lock Cipherclerk"; the initial
  // refresh() flips it to "Unlock Cipherclerk" for the locked-at-rest clerk.
  // Wait for that refresh to land before deciding (the passphrase section is
  // unhidden in the same render).
  await popup.locator('#passphraseSection:not(.hidden), #backupBtn[style*="block"]')
    .first().waitFor({ state: 'attached', timeout: 5000 });
  if ((await lockBtn.textContent())?.includes('Unlock')) {
    await popup.fill('#passphraseInput', 'e2e');
    await lockBtn.click();
    // Exact comparison: hasText would substring-match "Unlock Cipherclerk".
    await popup.waitForFunction(
      () => document.getElementById('lockBtn')?.textContent === 'Lock Cipherclerk',
      null,
      { timeout: 5000 },
    );
  }
}
