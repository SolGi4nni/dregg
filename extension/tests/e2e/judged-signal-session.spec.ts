/**
 * THE JUDGED RUN, DRIVEN ACROSS THE PAGE↔EXTENSION SEAM FOR REAL — and the three
 * walls that stop the same run reaching a node.
 *
 * # What this drives, and what it does NOT
 *
 * ⚑ SAY THE STUBS OUT LOUD, because the brief this file answers asked for a
 * page → extension → node run and only two of those three hops are reachable
 * today.
 *
 * REAL here, no stub anywhere in the loop:
 *   - the PAGE layer is `poa-web/src/judged-session.js` ITSELF, served off disk
 *     and imported as a module. `requestSessionSignature` and the statement
 *     encoders are the shipped ones; this file re-implements neither.
 *   - the ORIGIN is genuinely `https://beta.pathofangels.network` — the bytes are
 *     fulfilled by the test, but `window.location.origin` is the real thing, so
 *     every origin gate in `content.ts` sees what it would see on the beta host.
 *   - the EXTENSION is the real unpacked MV3 build under `extension/`, with the
 *     real service worker, the real content script, the real `window.dregg`, the
 *     real Cipherclerk custody and the real consent popups.
 *   - the SIGNATURE is a real Ed25519 signature by the extension-held player key,
 *     and this file verifies it with `node:crypto` against the statement bytes
 *     THE PAGE derived — not against bytes the extension handed back.
 *
 * NOT DRIVEN HERE — and not faked either:
 *   - the NODE hop. There is no judged node in this run. `open` / `guess` /
 *     read-back are never POSTed, because a judged node cannot be stood up for a
 *     browser to reach (see WALL 0 below), and a hand-written JS "node" that
 *     classified LOCKED/DRIFT would be a second copy of the Lean feedback oracle
 *     — the exact twin this repo spends its time deleting. So the node-side of
 *     the run is covered where it already is: `node/src/poa_signal_session_e2e.rs`
 *     drives it in-process through the real router, both poles.
 *
 * # ⚑ THE HEADLINE, and it was found by DRIVING and by nothing else
 *
 * **A judged run cannot be PLAYED from a browser at all** — never mind settled.
 * `dregg:signSignalSession` is missing from `PAGE_ALLOWED_METHODS` in
 * `background.ts`, so every page call is refused with
 * `"dregg:signSignalSession" is not available from page context.` The signer
 * `bff85f1fc` wired — grant book, scoped popup, budget, the lot — is unreachable
 * from any page. `dregg:signOfferingTurn` is dead at the same gate.
 *
 * Reading the two sides could not find this: `page.ts` exposes the method,
 * `content.ts` restricts it, `background.ts` implements it. Every side is right.
 * The *third* list is the one that decides, and nobody was on it. Measured: with
 * that ONE Set entry added to a COPY of the extension, the five seam tests below
 * go from red to green and the whole run signs — 9/9 against the patched copy,
 * 3/9 against this tree, and that delta IS the defect.
 *
 * See `the page-surface gates agree with each other` below, which asserts the
 * INVARIANT rather than the bug: it names both dead methods today and keeps
 * catching the class after the fix.
 *
 * # The three walls beyond it, each proved BEHAVIOURALLY below rather than asserted
 *
 * Even with the signer reachable, a judged run cannot be SETTLED from a browser,
 * and the reason is not one missing wire — it is three independent stops, any one
 * of which is terminal:
 *
 * WALL 0 — **the node cannot be stood up for a browser.** The Signal head and the
 *   curator pin are installed in-process only: `poa_signal_adapter::
 *   fixture_signal_head_for_finality_test` is `pub(crate)`, and the one CLI that
 *   installs a head — `dregg-node init-poa-signal` — demands the POAG1 catalog,
 *   which NAMES the live federation id and so refuses a locally minted one
 *   (`Poag1Bundle::bind_deployment_scope`, and the deviation stated in
 *   `poa_signal_slot_first_turn_rehearsal.rs`). Not asserted here: it is an
 *   absence, and this file cannot make an absence go red.
 *
 * WALL 1 — **the claim leg is pinned to the live deployment.** `POA_SIGNAL_
 *   FEDERATION_HEX` (`extension/src/poa-signal.ts`) is the live federation id and
 *   `background.ts` refuses any `/status` that does not report it, while
 *   `POA_SIGNAL_NODE_URL` is a FROZEN `NodeConfig` the user's node settings
 *   cannot swap. A locally genesised federation derives a different id from its
 *   own committee, so it can never satisfy the pin. The origin half of the same
 *   policy IS reachable, and is driven: see `refuses a claim off the beta origin`.
 *
 * WALL 2 — **the shipped wasm has no PoA Signal carrier at all.** `wasm/src/lib.rs`
 *   defines `build_poa_signal_claim_turn` / `inspect_poa_signal_claim_turn`, but
 *   the artifact the extension actually loads — `extension/dregg_wasm.js` +
 *   `dregg_wasm_bg.wasm` — carries 160 exports and NOT ONE of them is either. So
 *   `background.ts` refuses every claim by name, on the live beta too, not merely
 *   here. That is driven end to end below and it is the load-bearing test in this
 *   file: it is the wall that is invisible to reading both sides, because both
 *   sides are correct — it is the BUILD between them that is stale.
 *
 * ⚠ And a fourth, which is not a wall so much as an absence: `poa-web` never
 * calls `dregg.submitPoaSignalClaim` anywhere. The only occurrence of that name
 * in the whole web tree is inside a comment in `judged-session.js`. There is no
 * page-side caller of the settle path to drive, which is why the claim poles in
 * this file call `window.dregg` directly and say so.
 */
import { test, expect } from '../fixtures/extension';
import type { BrowserContext, Page } from '@playwright/test';
import { createVerify, verify as cryptoVerify } from 'crypto';
import { readFileSync } from 'fs';
import path from 'path';

const WEB_SRC = path.resolve(__dirname, '..', '..', '..', 'poa-web', 'src');

/** The exact origin `content.ts` and `background.ts` gate the claim path on. */
const BETA = 'https://beta.pathofangels.network';
/** Any other real origin — the off-beta pole. */
const ELSEWHERE = 'https://example.com';

/** A 32-byte authority id and a slot to play against. No node reads these here. */
const AUTHORITY = 'a3'.repeat(32);
const SLOT = 9;
const NEXT_SLOT = 10;

/** `POA_SIGNAL_SCHEMA` / `POA_SIGNAL_MISSION_ID` in `extension/src/poa-signal.ts`. */
const CLAIM_SCHEMA = 'poa-signal-claim/v1';
const MISSION_ID = 1;

/** Five bands per position; any legal code will do — nothing scores it here. */
const GUESSES: Array<[number, number, number]> = [
  [0, 1, 2], [1, 2, 3], [2, 3, 4], [3, 4, 5], [4, 5, 0],
];

/**
 * Serve the REAL `poa-web` module graph at the REAL beta origin.
 *
 * The route is on the worker-scoped context, so it is installed per test and
 * torn down after — a leaked route would serve this shell to every other spec
 * in the worker.
 */
async function serveBeta(context: BrowserContext): Promise<() => Promise<void>> {
  const shell = `<!doctype html><meta charset="utf-8"><title>judged run</title><body></body>`;
  const handler = async (route: import('@playwright/test').Route): Promise<void> => {
    const url = new URL(route.request().url());
    if (url.pathname.startsWith('/src/') && url.pathname.endsWith('.js')) {
      const file = path.join(WEB_SRC, path.basename(url.pathname));
      route.fulfill({
        status: 200,
        contentType: 'text/javascript; charset=utf-8',
        body: readFileSync(file, 'utf8'),
      });
      return;
    }
    route.fulfill({ status: 200, contentType: 'text/html; charset=utf-8', body: shell });
  };
  await context.route(`${BETA}/**`, handler);
  return async () => { await context.unroute(`${BETA}/**`, handler); };
}

/**
 * Open a page at `origin` with the real `judged-session.js` module loaded onto
 * `window.__judged`, and `window.dregg` present.
 */
async function openJudgedPage(context: BrowserContext, origin: string): Promise<Page> {
  const page = await context.newPage();
  await page.goto(`${origin}/`);
  await page.waitForFunction(() => 'dregg' in window, null, { timeout: 15000 });
  if (origin === BETA) {
    await page.evaluate(async () => {
      (window as unknown as Record<string, unknown>).__judged =
        await import('/src/judged-session.js');
    });
  }
  return page;
}

/**
 * Approve the origin-permission popup if it is the one that opened, and hand
 * back the confirm-intent popup when it arrives. Returns `null` when no popup
 * opened within `settle` ms — which is how "one consent covered this" is
 * OBSERVED rather than assumed.
 */
async function approveIfPrompted(
  context: BrowserContext,
  settle = 2500,
): Promise<{ sawOriginPrompt: boolean; confirm: Page | null }> {
  let sawOriginPrompt = false;
  let popup: Page | null = null;
  try {
    popup = await context.waitForEvent('page', {
      predicate: (p) =>
        p.url().includes('origin-permission.html') || p.url().includes('confirm-intent.html'),
      timeout: settle,
    });
  } catch {
    return { sawOriginPrompt: false, confirm: null };
  }
  await popup.waitForLoadState('domcontentloaded');
  if (popup.url().includes('origin-permission.html')) {
    sawOriginPrompt = true;
    await popup.click('#allowBtn');
    try {
      popup = await context.waitForEvent('page', {
        predicate: (p) => p.url().includes('confirm-intent.html'),
        timeout: 15000,
      });
      await popup.waitForLoadState('domcontentloaded');
    } catch {
      return { sawOriginPrompt, confirm: null };
    }
  }
  return { sawOriginPrompt, confirm: popup };
}

/** Click the accept control on a confirm-intent popup, whatever it is called. */
async function acceptConsent(popup: Page): Promise<void> {
  const candidates = ['#confirmBtn', '#approveBtn', '#allowBtn', '#signBtn', 'button#confirm'];
  for (const selector of candidates) {
    const handle = await popup.$(selector);
    if (handle) {
      await handle.click();
      return;
    }
  }
  // Fall back to the first enabled button whose label reads as an approval.
  const clicked = await popup.evaluate(() => {
    const buttons = [...document.querySelectorAll('button')] as HTMLButtonElement[];
    const accept = buttons.find(
      (b) => !b.disabled && /confirm|approve|sign|allow|accept/i.test(b.textContent || ''),
    );
    if (!accept) return false;
    accept.click();
    return true;
  });
  if (!clicked) {
    throw new Error(
      `no accept control on ${popup.url()}; buttons were: ` +
        JSON.stringify(
          await popup.evaluate(() =>
            [...document.querySelectorAll('button')].map((b) => (b as HTMLButtonElement).textContent),
          ),
        ),
    );
  }
}

/**
 * Ask the page — through the REAL `requestSessionSignature` — for one session
 * signature, driving whatever consent surface the extension raises.
 */
async function signThroughThePage(
  context: BrowserContext,
  page: Page,
  request: { kind: 'open' | 'guess'; slot: number; round?: number; guess?: [number, number, number] },
  settle = 2500,
): Promise<{ result: Record<string, unknown>; confirmText: string | null; sawConfirm: boolean }> {
  await page.evaluate((req) => {
    const w = window as unknown as Record<string, any>;
    w.__signed = undefined;
    const guess = req.guess ? { low: req.guess[0], mid: req.guess[1], high: req.guess[2] } : null;
    w.__judged
      .requestSessionSignature({
        provider: w.dregg,
        kind: req.kind,
        authorityId: req.authorityId,
        slot: req.slot,
        round: req.round ?? null,
        guess,
      })
      .then((r: unknown) => { w.__signed = r; })
      .catch((e: Error) => { w.__signed = { state: 'threw', reason: String(e && e.message) }; });
  }, { ...request, authorityId: AUTHORITY });

  const { confirm } = await approveIfPrompted(context, settle);
  let confirmText: string | null = null;
  if (confirm) {
    confirmText = await confirm.evaluate(() => document.body.innerText);
    await acceptConsent(confirm);
  }
  await page.waitForFunction(() => (window as any).__signed !== undefined, null, { timeout: 20000 });
  const result = await page.evaluate(() => (window as any).__signed as Record<string, unknown>);
  return { result, confirmText, sawConfirm: confirm !== null };
}

/** Verify a raw Ed25519 signature over `message` under a raw 32-byte public key. */
function ed25519Verifies(publicKeyHex: string, message: string, signatureHex: string): boolean {
  // Wrap the raw key in the fixed SPKI prefix for id-Ed25519 so node:crypto
  // will take it — the extension hands back raw bytes, as the node expects.
  const spki = Buffer.concat([
    Buffer.from('302a300506032b6570032100', 'hex'),
    Buffer.from(publicKeyHex, 'hex'),
  ]);
  const key = {
    key: `-----BEGIN PUBLIC KEY-----\n${spki.toString('base64')}\n-----END PUBLIC KEY-----\n`,
    format: 'pem' as const,
  };
  void createVerify; // ed25519 is one-shot only; `verify` is the right entry.
  return cryptoVerify(
    null,
    Buffer.from(message, 'utf8'),
    key,
    Buffer.from(signatureHex, 'hex'),
  );
}

let unserve: (() => Promise<void>) | null = null;

test.beforeEach(async ({ context }) => {
  // The config's 15s default is sized for tests that only click. These drive a
  // whole six-signature run and must WAIT OUT the settle window on each burst to
  // observe that no popup opened — proving the grant covered it. That waiting is
  // the measurement, so the budget has to hold six of them.
  test.setTimeout(120_000);
  unserve = await serveBeta(context);
});

test.afterEach(async ({ context }) => {
  if (unserve) await unserve();
  unserve = null;
  // A test that fails mid-run leaves its consent popup open, and the worker
  // context is shared with every other spec — an accumulating pile of popups
  // turns one red into a fixture-teardown timeout that hides which test failed.
  for (const page of context.pages()) {
    if (page.isClosed()) continue;
    const url = page.url();
    if (url.includes('confirm-intent.html') || url.includes('origin-permission.html')
        || url.startsWith(BETA) || url.startsWith(ELSEWHERE)) {
      await page.close().catch(() => { /* already gone */ });
    }
  }
});

test.describe('the page↔extension seam of a judged run', () => {
  test('the page gets a real Ed25519 signature over the statement IT derived', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);
    const { result } = await signThroughThePage(context, page, { kind: 'open', slot: SLOT });

    // `signed` is the ONLY state `requestSessionSignature` reaches when the
    // extension's re-derivation and the page's `openStatementMessage` produce
    // identical bytes — a drift lands as `session-statement-mismatch` instead.
    // So this single assertion is the cross-derivation check, driven.
    expect(result.state, JSON.stringify(result)).toBe('signed');
    const playerKey = result.playerKey as string;
    const statement = result.statement as string;
    const signature = result.signature as string;
    expect(playerKey).toMatch(/^[0-9a-f]{64}$/);
    expect(signature).toMatch(/^[0-9a-f]{128}$/);

    // The page's OWN encoder, re-run here, must be what got signed.
    const expected = await page.evaluate(
      ([authorityId, slot, key]) =>
        (window as any).__judged.openStatementMessage({ authorityId, slot, playerKey: key }),
      [AUTHORITY, SLOT, playerKey] as const,
    );
    expect(statement).toBe(expected);
    expect(statement).toContain('"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1"');

    // And the signature is real: verified here against the page's bytes, under
    // the extension's key, by a verifier neither layer wrote.
    expect(ed25519Verifies(playerKey, expected, signature)).toBe(true);
    await page.close();
  });

  test('ONE consent covers the whole run: open + five guesses, and a sixth re-prompts', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);

    const opened = await signThroughThePage(context, page, { kind: 'open', slot: SLOT });
    expect(opened.result.state, JSON.stringify(opened.result)).toBe('signed');
    expect(opened.sawConfirm).toBe(true);
    const playerKey = opened.result.playerKey as string;

    // The grant's budget is 1 open + 5 guesses. Every one of these five must be
    // signed WITHOUT a further popup, or the grant is not a grant.
    for (let round = 0; round < GUESSES.length; round++) {
      const spent = await signThroughThePage(context, page, {
        kind: 'guess', slot: SLOT, round, guess: GUESSES[round],
      });
      expect(spent.result.state, `round ${round}: ${JSON.stringify(spent.result)}`).toBe('signed');
      expect(spent.sawConfirm, `round ${round} must be covered by the run grant`).toBe(false);
      expect(
        ed25519Verifies(playerKey, spent.result.statement as string, spent.result.signature as string),
      ).toBe(true);
    }

    // A SIXTH guess is past the budget. The failure direction must be a popup,
    // never a silent signature.
    const sixth = await signThroughThePage(context, page, {
      kind: 'guess', slot: SLOT, round: 5, guess: [5, 4, 3],
    });
    expect(sixth.sawConfirm, 'a sixth burst is outside the granted budget and must ask again').toBe(true);
    await page.close();
  });

  test('the consent popup names the GRANT SCOPE, not just the burst in front of it', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);
    const { result, confirmText } = await signThroughThePage(context, page, { kind: 'open', slot: SLOT });
    expect(result.state, JSON.stringify(result)).toBe('signed');
    expect(confirmText, 'the open must raise a confirm-intent popup').not.toBeNull();

    // `bindingHex` binds ONE statement; the grant authorizes six. A popup that
    // shows only the binding displays consent for less than it grants.
    const text = (confirmText as string).replace(/\s+/g, ' ');
    expect(text).toMatch(/\b5\b|\bfive\b/i);
    expect(text.toLowerCase()).toContain('guess');
    expect(text).toContain(String(SLOT));
    await page.close();
  });

  test('a slot-N grant is useless at slot N+1', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);
    const opened = await signThroughThePage(context, page, { kind: 'open', slot: SLOT });
    expect(opened.result.state, JSON.stringify(opened.result)).toBe('signed');
    expect(opened.sawConfirm).toBe(true);

    // Same authority, same origin, same identity — a DIFFERENT slot. The grant
    // compares slot for equality, so this must fall back to asking.
    const nextSlot = await signThroughThePage(context, page, { kind: 'open', slot: NEXT_SLOT });
    expect(nextSlot.sawConfirm, 'a grant for slot 9 must not cover slot 10').toBe(true);
    expect(nextSlot.result.state, JSON.stringify(nextSlot.result)).toBe('signed');
    expect(nextSlot.result.statement as string).toContain(`"slot":${NEXT_SLOT}`);
    await page.close();
  });

  test('the signer hands back a statement and nothing else — no instance rides along', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);

    // The RAW signer, driven once directly, so the field set the extension
    // returns is observed rather than the page's re-shaped view of it. A signer
    // that handed an instance, a seed or a target back alongside the signature
    // would show up as an extra key here.
    await page.evaluate(([authorityId, slot]) => {
      const w = window as unknown as Record<string, any>;
      w.__raw = undefined;
      w.dregg
        .signSignalSession({ kind: 'open', authorityId, slot })
        .then((r: Record<string, unknown>) => { w.__raw = { keys: Object.keys(r).sort(), value: r }; })
        .catch((e: Error) => { w.__raw = { error: String(e && e.message) }; });
    }, [AUTHORITY, SLOT] as const);

    const { confirm } = await approveIfPrompted(context, 15000);
    expect(confirm, 'the first open from this origin must raise a consent popup').not.toBeNull();
    await acceptConsent(confirm as Page);
    await page.waitForFunction(() => (window as any).__raw !== undefined, null, { timeout: 20000 });
    const raw = await page.evaluate(() => (window as any).__raw as Record<string, unknown>);

    expect(raw.error, JSON.stringify(raw)).toBeUndefined();
    expect(raw.keys).toEqual(['kind', 'playerKeyHex', 'schema', 'signatureHex', 'statement']);

    // And the statement itself is `{schema, authority_id, slot, player_key}` and
    // NOTHING ELSE — no instance, no seed, no target.
    const value = raw.value as Record<string, string>;
    const parsed = JSON.parse(value.statement) as Record<string, unknown>;
    expect(Object.keys(parsed).sort()).toEqual(['authority_id', 'player_key', 'schema', 'slot']);
    await page.close();
  });
});

/**
 * WALL 3 — THE ONE THIS FILE FOUND BY DRIVING IT, and the class it belongs to.
 *
 * `dregg.signSignalSession` is exposed on `page.ts`, is listed in `content.ts`'s
 * `RESTRICTED_METHODS` (so it raises a consent popup and a per-origin grant), is
 * fully handled in `background.ts` (the grant book, the popup, the signing) — and
 * is ABSENT from `background.ts`'s `PAGE_ALLOWED_METHODS`, which is the gate the
 * request actually meets. Every page call dies at
 * `"dregg:signSignalSession" is not available from page context.`
 * before any of that machinery runs. `dregg.signOfferingTurn` is in the same
 * state. Both compile; both were wired end to end everywhere except the one Set
 * that decides.
 *
 * ⚑ This is asserted as the INVARIANT rather than as the bug, deliberately. A
 * test that pinned "these two are missing" would have to be deleted by the fix;
 * this one goes GREEN on the fix and keeps catching the whole class afterwards —
 * a page-exposed, origin-restricted method that nobody added to the allowlist.
 */
test.describe('the page-surface gates agree with each other', () => {
  test('every page-exposed restricted method is reachable from page context', async () => {
    const SRC = path.resolve(__dirname, '..', '..', 'src');
    const content = readFileSync(path.join(SRC, 'content.ts'), 'utf8');
    const background = readFileSync(path.join(SRC, 'background.ts'), 'utf8');

    const block = (text: string, marker: string): string => {
      const start = text.indexOf(marker);
      expect(start, `${marker} moved; re-anchor this test`).toBeGreaterThan(-1);
      const end = text.indexOf(']);', start);
      expect(end, `${marker} is not a Set literal any more; re-anchor this test`).toBeGreaterThan(start);
      return text.slice(start, end);
    };
    const names = (text: string): string[] =>
      [...text.matchAll(/"(dregg:[A-Za-z]+)"/g)].map((m) => m[1]);

    const restricted = names(block(content, 'const RESTRICTED_METHODS = new Set<MessageType>(['));
    const allowed = new Set(names(block(background, 'const PAGE_ALLOWED_METHODS = new Set<MessageType>([')));
    expect(restricted.length).toBeGreaterThan(10);
    expect(allowed.size).toBeGreaterThan(10);

    // A method the content script will forward for a consented origin, but the
    // background will not accept from a content script, is dead on arrival — the
    // consent popup is raised and then the answer is a flat refusal.
    const unreachable = restricted.filter((m) => !allowed.has(m));
    expect(
      unreachable,
      'these methods raise a per-origin consent prompt and are then refused by ' +
        'PAGE_ALLOWED_METHODS — the page can never actually call them',
    ).toEqual([]);
  });
});

test.describe('the settle leg: both refusal poles, by name', () => {
  test('WALL 1 (origin half) — a claim off the beta origin is refused before any popup', async ({ context }) => {
    const page = await openJudgedPage(context, ELSEWHERE);
    const popups: string[] = [];
    context.on('page', (p) => popups.push(p.url()));

    const outcome = await page.evaluate(async ([schema, missionId]) => {
      try {
        await (window as any).dregg.submitPoaSignalClaim({
          schema, missionId, transcript: [[0, 1, 2], [1, 2, 3]],
        });
        return { refused: false, message: '' };
      } catch (e: any) {
        return { refused: true, message: String(e && e.message) };
      }
    }, [CLAIM_SCHEMA, MISSION_ID] as const);

    expect(outcome.refused, 'an off-beta origin must not be able to settle').toBe(true);
    expect(outcome.message).toContain('beta.pathofangels.network');
    expect(popups.filter((u) => u.includes('.html'))).toHaveLength(0);
    await page.close();
  });

  test('WALL 2 — at the beta origin, the SHIPPED wasm carries no PoA Signal builder', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);

    await page.evaluate(([schema, missionId]) => {
      const w = window as unknown as Record<string, any>;
      w.__claim = undefined;
      w.dregg
        .submitPoaSignalClaim({ schema, missionId, transcript: [[0, 1, 2], [1, 2, 3]] })
        .then((r: unknown) => { w.__claim = r; })
        .catch((e: Error) => { w.__claim = { error: String(e && e.message), threw: true }; });
    }, [CLAIM_SCHEMA, MISSION_ID] as const);

    // The origin gate passes here (this IS beta), so the first popup is the
    // per-method origin permission. Approving it is what lets the request reach
    // the background — and the wall.
    await approveIfPrompted(context, 15000);
    await page.waitForFunction(() => (window as any).__claim !== undefined, null, { timeout: 30000 });
    const claim = await page.evaluate(() => (window as any).__claim as Record<string, unknown>);

    // ⚑ THE LOAD-BEARING ASSERTION OF THIS FILE. Both sides are correct and the
    // BUILD between them is stale: `wasm/src/lib.rs` exports
    // `build_poa_signal_claim_turn`, the artifact under `extension/` does not.
    // This refusal is what a player on the LIVE beta gets today.
    expect(String(claim.error), JSON.stringify(claim)).toContain(
      'installed dregg WASM does not include the PoA Signal carrier',
    );
    await page.close();
  });

  test('WALL 2, read off the artifact itself — the carrier is absent from the shipped glue', async () => {
    const glue = readFileSync(
      path.resolve(__dirname, '..', '..', 'dregg_wasm.js'),
      'utf8',
    );
    // The behavioural pole above says the extension refuses; this says WHY, in
    // the artifact, so a rebuild that fixes one fixes both and neither can go
    // green while the other is red.
    expect(glue).not.toContain('build_poa_signal_claim_turn');
    expect(glue).not.toContain('inspect_poa_signal_claim_turn');
    // …and it is a stale BUILD, not a missing feature: the source defines them.
    const source = readFileSync(
      path.resolve(__dirname, '..', '..', '..', 'wasm', 'src', 'lib.rs'),
      'utf8',
    );
    expect(source).toContain('pub fn build_poa_signal_claim_turn');
  });
});
