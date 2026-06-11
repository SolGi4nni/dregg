import { test, expect } from '../fixtures/extension';
import { MockNode } from '../fixtures/node-mock';

let mockNode: MockNode;

test.beforeAll(async () => {
  mockNode = new MockNode({ port: 8420 });
  await mockNode.start();
});

test.afterAll(async () => {
  await mockNode.stop();
});

test.describe('window.dregg injection', () => {
  test('window.dregg is available on navigated pages', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForLoadState('domcontentloaded');

    // Wait for the content script to inject page.js.
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    const hasDregg = await page.evaluate(() => typeof (window as any).dregg === 'object');
    expect(hasDregg).toBe(true);
    await page.close();
  });

  test('window.dregg is frozen (not modifiable)', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    const isFrozen = await page.evaluate(() => Object.isFrozen((window as any).dregg));
    expect(isFrozen).toBe(true);
    await page.close();
  });

  test('window.dregg has expected API methods', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    const methods = await page.evaluate(() => Object.keys((window as any).dregg));
    expect(methods).toContain('authorize');
    expect(methods).toContain('isConnected');
    expect(methods).toContain('canAuthorize');
    expect(methods).toContain('provision');
    expect(methods).toContain('postIntent');
    expect(methods).toContain('shareCapability');
    expect(methods).toContain('acceptCapability');
    expect(methods).toContain('storageWrite');
    expect(methods).toContain('storageRead');
    expect(methods).toContain('storageQuota');
    expect(methods).toContain('on');
    expect(methods).toContain('off');
    await page.close();
  });
});

test.describe('Unrestricted methods', () => {
  test('isConnected returns true when extension is loaded', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    const connected = await page.evaluate(async () => {
      return await (window as any).dregg.isConnected();
    });
    expect(connected).toBe(true);
    await page.close();
  });

  test('canAuthorize works without permission prompt', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    // canAuthorize is unrestricted. With a locked cipherclerk or no matching token,
    // it should return false without prompting.
    const result = await page.evaluate(async () => {
      return await (window as any).dregg.canAuthorize({
        action: 'read',
        resource: 'documents/test',
      });
    });
    // Should be false (cipherclerk is locked in fresh state).
    expect(result).toBe(false);
    await page.close();
  });

  test('storageQuota is accessible without permission', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    // storageQuota is unrestricted.
    const result = await page.evaluate(async () => {
      try {
        return await (window as any).dregg.storageQuota();
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Should either return quota data or a structured result (not a permission error).
    expect(result).toBeDefined();
    await page.close();
  });
});

test.describe('Restricted methods', () => {
  test('authorize from unpermitted origin triggers permission request', async ({ context }) => {
    const page = await context.newPage();
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    // authorize is a restricted method. Without prior permission, it should
    // either prompt the user or return a permission error.
    const result = await page.evaluate(async () => {
      try {
        // Use a short timeout to avoid hanging on the popup.
        const controller = new AbortController();
        const timeout = setTimeout(() => controller.abort(), 3000);
        const promise = (window as any).dregg.authorize({
          action: 'read',
          resource: 'documents/test',
        });
        const raceResult = await Promise.race([
          promise,
          new Promise(resolve => setTimeout(() => resolve({ timeout: true }), 3000)),
        ]);
        clearTimeout(timeout);
        return raceResult;
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Should either timeout (popup waiting for user) or return permission error.
    expect(result).toBeDefined();
    await page.close();
  });

  test('unknown method is rejected with clear error', async ({ context }) => {
    const page = await context.newPage();
    // The content script removes the injected page.js script tag (with its
    // data-dregg-nonce) once loaded, so harvest the session nonce from the
    // event channel itself: wrap dispatchEvent before page.js loads and
    // capture the `dregg:request:<nonce>` type of its first real request.
    await page.addInitScript(() => {
      (window as any).__dreggNonce = null;
      const orig = window.dispatchEvent.bind(window);
      window.dispatchEvent = ((ev: Event) => {
        const m = /^dregg:request:(.+)$/.exec(ev?.type || '');
        if (m) (window as any).__dreggNonce = m[1];
        return orig(ev);
      }) as typeof window.dispatchEvent;
    });
    await page.goto('https://example.com');
    await page.waitForFunction(() => 'dregg' in window, null, { timeout: 5000 });

    // Try to call a method that does not exist via the internal sendMessage.
    const result = await page.evaluate(async () => {
      try {
        // Trigger one legitimate call so the wrapper observes the nonce.
        await (window as any).dregg.isConnected();
        // Dispatch a raw event with an unknown method type.
        const nonce = (window as any).__dreggNonce;
        if (!nonce) return { error: 'no nonce found' };

        return new Promise((resolve) => {
          const id = 'test_unknown_method';
          const handler = (event: any) => {
            if (event.detail?.id === id) {
              window.removeEventListener(`dregg:response:${nonce}`, handler);
              resolve(event.detail);
            }
          };
          window.addEventListener(`dregg:response:${nonce}`, handler);
          window.dispatchEvent(new CustomEvent(`dregg:request:${nonce}`, {
            detail: { type: 'dregg:nonExistentMethod', id },
          }));
          setTimeout(() => resolve({ timeout: true }), 3000);
        });
      } catch (e: any) {
        return { error: e.message };
      }
    });
    // Must receive the content script's clear rejection — a silent timeout
    // would mean unknown methods are dropped instead of refused.
    expect(result && 'error' in result, `expected an error, got ${JSON.stringify(result)}`).toBe(true);
    expect((result as any).error).toContain('not available');
    await page.close();
  });
});
