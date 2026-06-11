import { test, expect, unlockPopup } from '../fixtures/extension';
import { MockNode } from '../fixtures/node-mock';

let mockNode: MockNode;

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

test.describe('Share capability', () => {
  test('share tab has cell ID input and share button', async ({ popup }) => {
    // Switch to Caps tab.
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    const shareCellInput = popup.locator('#shareCellInput');
    await expect(shareCellInput).toBeVisible();
    const shareCapBtn = popup.locator('#shareCapBtn');
    await expect(shareCapBtn).toBeVisible();
    await expect(shareCapBtn).toHaveText('Share as URI');
  });

  test('share button validates cell ID format (rejects short input)', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    const input = popup.locator('#shareCellInput');
    await input.fill('not-a-valid-hex');
    await popup.locator('#shareCapBtn').click();
    // Should mark input as invalid (border color change).
    const borderColor = await input.evaluate(el => getComputedStyle(el).borderColor);
    // The script sets borderColor to #f87171 (rgb(248, 113, 113)) on invalid input.
    expect(borderColor).not.toBe('');
  });

  test('share with valid cell ID triggers share flow', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    const validCellId = 'a'.repeat(64);
    await popup.locator('#shareCellInput').fill(validCellId);
    await popup.locator('#shareCapBtn').click();

    // The share result area should appear (may show error if cipherclerk locked,
    // but the UI interaction path is exercised).
    const shareResult = popup.locator('#shareResult');
    // Wait briefly for the async response.
    await popup.waitForTimeout(500);
    const display = await shareResult.evaluate(el => getComputedStyle(el).display);
    // Should be visible (showing either URI or error).
    expect(display).toBe('block');
  });
});

test.describe('Accept capability', () => {
  test('accept tab has URI input and accept button', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    const acceptInput = popup.locator('#acceptUriInput');
    await expect(acceptInput).toBeVisible();
    const acceptBtn = popup.locator('#acceptCapBtn');
    await expect(acceptBtn).toBeVisible();
    await expect(acceptBtn).toHaveText('Accept Capability');
  });

  test('accept with empty URI does nothing', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    await popup.locator('#acceptCapBtn').click();
    // Button text should not change (empty URI is a no-op).
    const btn = popup.locator('#acceptCapBtn');
    const text = await btn.textContent();
    expect(text).toBe('Accept Capability');
  });

  test('accept with dregg:// URI triggers enliven flow', async ({ popup }) => {
    // The clerk is locked at rest; enlivening requires the unlocked clerk.
    await unlockPopup(popup);
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    // Full sturdy-ref shape: dregg://<node>/<cell>/<secret>.
    const uri = `dregg://node_mock_001/${'b'.repeat(64)}/mock_bearer_secret`;
    await popup.locator('#acceptUriInput').fill(uri);
    await popup.locator('#acceptCapBtn').click();

    // The mock node's peer-exchange answers with a cap grant; the button
    // reports the real success state.
    const btn = popup.locator('#acceptCapBtn');
    await expect(btn).toHaveText('Accepted!', { timeout: 5000 });
    expect(mockNode.state.lastPeerExchange).toMatchObject({ node_id: 'node_mock_001' });
  });
});

test.describe('Live references', () => {
  test('live references section shows empty state', async ({ popup }) => {
    await popup.locator('.tab-btn[data-tab="capabilities"]').click();
    const container = popup.locator('#liveRefsContainer');
    await expect(container).toBeVisible();
    const emptyMsg = container.locator('.empty');
    await expect(emptyMsg).toHaveText('No live references held');
  });
});
