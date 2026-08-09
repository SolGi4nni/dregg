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
 * # ⚑ WHERE THE CHAIN STOPS TODAY, and every step of it was found by DRIVING
 *
 * Three walls this file used to assert have FALLEN, and each is now asserted as
 * the INVARIANT rather than as the bug — so the fix made them green instead of
 * making them deletable, and they keep catching a regression:
 *
 * FELL — **the page allowlist.** `dregg:signSignalSession` was missing from
 *   `PAGE_ALLOWED_METHODS`, so the scoped signer `bff85f1fc` wired was
 *   unreachable from any page and a judged run could not be PLAYED at all.
 *   Reading the two sides could not find it: `page.ts` exposes the method,
 *   `content.ts` restricts it, `background.ts` implements it — every side right,
 *   and the *third* list is the one that decides. `30576afde`. The invariant
 *   form is `the page-surface gates agree with each other` below.
 *
 * FELL — **the session routes.** They are in `public_routes` now; a player's
 *   Ed25519 signature over a statement the node re-derives was always the
 *   authorization, and the bearer never was.
 *
 * FELL — **the shipped wasm carrier.** `extension/dregg_wasm.js` carried 160
 *   exports and neither `build_poa_signal_claim_turn` nor its inspector, so the
 *   background refused every claim by name — on live beta too. `84907fcf4` made
 *   the bundle BUILT rather than found in the tree; it carries the pair now.
 *
 * ⚑ AND THE ABSENCE IS CLOSED. This note used to end "`poa-web` never calls
 * `dregg.submitPoaSignalClaim` anywhere; the only occurrence of that name in the
 * whole web tree is inside a comment." It does now: `judged-session.js` exports
 * `settleJudgedRun`, and `the settle leg, driven through the real poa-web caller`
 * below drives THAT — the shipped page function, served off disk — rather than
 * `window.dregg` directly.
 *
 * # WALL A FELL on 2026-08-09, and what stands is no longer on this side of the wire
 *
 * FELL — **the extension can derive the player's cell now.** This was the one the
 *   chain hit. `background.ts::clientCellIdHex` calls
 *   `wasm.cell_id_for_pubkey(pubkeyHex, "default")` behind a `typeof …` probe
 *   that falls through to `return null`, and that function had never existed in
 *   any SHIPPED bundle. So every claim ever submitted refused at `Could not
 *   derive the active player's canonical cell`, on live beta too, and nothing
 *   said a function had been looked for and not found. It was INVISIBLE until
 *   the carrier wall fell, because it sits behind it. The binding landed in
 *   `wasm/src/lib.rs` in `c71edfbe2`; the bundle was rebuilt against it
 *   (`cd extension && ./build.sh wasm`, provenance `git 29951ddba`), and
 *   `check-wasm-freshness.sh` is GREEN. The artifact pole below generalized with
 *   the fix rather than going green on one name: it now sweeps EVERY function
 *   the background probes for and requires the shipped glue to carry it.
 *
 * ⚑ WHAT STOPS THE CHAIN TODAY IS THE NODE HOP, and it is TWO walls, not one.
 *
 * WALL B0 — **the private-beta Basic-auth curtain.** MEASURED 2026-08-09: every
 *   path on `node.pathofangels.network` answers `HTTP 401` with
 *   `www-authenticate: Basic realm="restricted"` and `server: Caddy` — `/`,
 *   `/status`, `/health`, all of them. `dregg-infra`'s
 *   `edge/anchor/Caddyfile` puts `basic_auth` at site-block top level with NO
 *   path matcher, so the node's `public_routes` never get to answer; the same
 *   curtain covers `beta.pathofangels.network`. It has been there since
 *   2026-08-02 and is NOT the re-genesis — it is the standing private-beta
 *   posture, asserted deliberately in three places and pinned by a test in that
 *   repo. `background.ts` carries no Basic credential BY DESIGN. THIS IS WHAT
 *   THE SEAM REPORTS NOW, and it refuses before WALL B is reached.
 *
 *   ⚑ The PAGE is not blocked by this and the EXTENSION is, which is the whole
 *   asymmetry: `judged-session.js` fetches `"/node" + path` with
 *   `credentials: "same-origin"` through Caddy's `handle_path /node/*` tunnel on
 *   the beta origin, so a player already past the curtain carries it for free.
 *   `POA_SIGNAL_NODE_URL` is the DIRECT host, a different origin, with no
 *   credential. Opening and playing a judged run from the page is reachable for
 *   an invited player; SETTLING through the extension is not.
 *
 * WALL B — **the node hop is pinned to the live deployment.** `POA_SIGNAL_
 *   FEDERATION_HEX` (`extension/src/poa-signal.ts`) is the live federation id and
 *   `background.ts` refuses any `/status` that does not report it, while
 *   `POA_SIGNAL_NODE_URL` is a FROZEN `NodeConfig` the user's node settings
 *   cannot swap. A locally genesised federation derives a different id from its
 *   own committee, so it can never satisfy the pin. The origin half of the same
 *   policy IS reachable, and is driven: see `refuses a claim off the beta origin`.
 *   ⚠ Still not reached today — WALL B0 refuses at the proxy, one step earlier.
 *
 * ⚠ STILL NOT DRIVEN AND STILL NOT FAKED: the node hop. There is no judged node
 * in this run. A hand-written JS "node" that classified LOCKED/DRIFT would be a
 * second copy of the Lean feedback oracle — the exact twin this repo spends its
 * time deleting. The node side is covered where it already is:
 * `node/src/poa_signal_session_e2e.rs` drives it in-process through the real
 * router, both poles.
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

  test('WALL 2 FELL, and the wall BEHIND it is what the seam now reports', async ({ context }) => {
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

    // ⚑ THE CARRIER WALL IS GONE. This assertion used to require exactly this
    // string; `84907fcf4` made the bundle BUILT and it stopped being reachable.
    // Asserted as the INVARIANT, so it keeps catching a regression to a stale
    // bundle instead of having to be deleted by the fix.
    expect(String(claim.error), JSON.stringify(claim)).not.toContain(
      'installed dregg WASM does not include the PoA Signal carrier',
    );

    // ⚑ AND THE CELL WALL IS GONE TOO, 2026-08-09. `clientCellIdHex` calls
    // `wasm.cell_id_for_pubkey` behind a probe that returned `null` instead of
    // saying so, and that function had never existed in any SHIPPED bundle — so
    // every claim ever submitted refused here, on live beta too. The binding
    // landed in `wasm/src/lib.rs` in `c71edfbe2` and the bundle was rebuilt
    // against it; the artifact pole above is what keeps that true.
    //
    // Same discipline as the line above: asserted as the INVARIANT, so a
    // regression to a stale bundle reds here rather than deleting a test.
    expect(String(claim.error), JSON.stringify(claim)).not.toContain(
      "Could not derive the active player's canonical cell",
    );

    // ⚑ AND THE STOP IS NOW THE NODE HOP, four steps further in — the first stop
    // this file has ever reached that is not a fact about a local artifact.
    //
    // MEASURED 2026-08-09: the refusal is `PoA Signal authority is unreachable:
    // HTTP 401:`. That 401 is NOT the node and NOT WALL B's federation pin — it
    // is the private-beta Basic-auth curtain in `dregg-infra`'s Caddyfile, which
    // wraps `node.pathofangels.network` with no path matcher, so every path 401s
    // including `/` and `/status`. `background.ts` carries no Basic credential
    // BY DESIGN ("There is intentionally no Basic-Auth credential or shared beta
    // password here"), so the pin is never even reached.
    //
    // The assertion is deliberately NOT `toContain("HTTP 401")`: that would pin
    // this test to today's curtain and go falsely red the day the deployment
    // changes. What must stay true is the DIRECTION — whatever refuses now is a
    // fact about the NODE, not about a local artifact.
    if (claim.error !== undefined) {
      expect(String(claim.error), JSON.stringify(claim)).toContain('PoA Signal authority');
    }
    await page.close();
  });

  test('WALL 2/A, off the artifact — EVERY wasm function the background probes for SHIPS in the glue', async () => {
    const glue = readFileSync(
      path.resolve(__dirname, '..', '..', 'dregg_wasm.js'),
      'utf8',
    );
    const source = readFileSync(
      path.resolve(__dirname, '..', '..', '..', 'wasm', 'src', 'lib.rs'),
      'utf8',
    );
    const background = readFileSync(
      path.resolve(__dirname, '..', '..', 'src', 'background.ts'),
      'utf8',
    );

    // ⚑ THE INVARIANT, NOT THE INSTANCE — and the generalization is the point.
    // `cell_id_for_pubkey` was absent from every bundle that has ever shipped and
    // NOTHING SAID SO, because each call site probes with `typeof … === "function"`
    // and falls through to a `null` that reads as an ordinary negative result. A
    // test pinning that one name would go green on the rebuild and never catch the
    // next silent probe. So the question asked here is the class: is every function
    // the background PROBES FOR actually present in the artifact a player receives?
    const probed = [
      ...new Set(
        [...background.matchAll(/typeof\s+w\.([A-Za-z0-9_]+)\s*[!=]==\s*"function"/g)].map(
          (m) => m[1],
        ),
      ),
    ].sort();
    expect(probed.length, 'the `typeof w.…` probe pattern moved; re-anchor this test')
      .toBeGreaterThanOrEqual(3);
    expect(probed, 'the cell derivation is probed this way and must stay in the sweep')
      .toContain('cell_id_for_pubkey');

    const missingFromGlue = probed.filter((fn) => !glue.includes(fn));
    expect(
      missingFromGlue,
      'the background probes for these wasm functions behind a SILENT `typeof` guard and the ' +
        'SHIPPED glue does not export them — the probe falls through to null and the refusal ' +
        'a player sees names something else entirely',
    ).toEqual([]);

    // And SOURCE and ARTIFACT are asked SEPARATELY, which is the whole lesson of
    // the commit that fixed the carrier: the question is never "is the check
    // correct" but "is it looking at the artifact a user receives". A player runs
    // the bundle, not the source.
    expect(source).toContain('pub fn cell_id_for_pubkey');
    expect(source).toContain('pub fn build_poa_signal_claim_turn');
    expect(glue).toContain('build_poa_signal_claim_turn');
    expect(glue).toContain('inspect_poa_signal_claim_turn');
  });
});

/**
 * ⚑ THE SETTLE CALLER, DRIVEN — the absence this file called out is closed.
 *
 * The note at the top of this file used to end: "`poa-web` never calls
 * `dregg.submitPoaSignalClaim` anywhere. The only occurrence of that name in the
 * whole web tree is inside a comment." It does now. `judged-session.js` exports
 * `settleJudgedRun`, and the tests below drive THAT — the shipped page function,
 * served off disk at the real beta origin — rather than `window.dregg` directly.
 *
 * So the claim poles below are a PAGE → EXTENSION run for real. The node hop is
 * still not driven and is still not faked: see the stop each test asserts.
 */
test.describe('the settle leg, driven through the real poa-web caller', () => {
  /**
   * A solved session document, shaped exactly as `poa_signal_session.rs` serves
   * one. Nothing here classifies anything — `exact`/`present` are written as a
   * node that already scored them would have written them, which is the only way
   * this file is allowed to have them at all.
   */
  const solvedDocument = (authorityId: string, commitment: string, playerKey: string) => ({
    format: 'POA-SIGNAL-SESSION-1',
    judged: true,
    authority_id: authorityId,
    mission_id: MISSION_ID,
    slot: SLOT,
    slot_commitment: commitment,
    player_key: playerKey,
    max_rounds: 5,
    rounds_used: 2,
    rounds_remaining: 3,
    solved: true,
    open: false,
    transcript: [
      { guess: { low: 0, mid: 1, high: 2 }, exact: 1, present: 1 },
      { guess: { low: 3, mid: 3, high: 3 }, exact: 3, present: 0 },
    ],
    settlement: {
      mission_id: MISSION_ID,
      transcript: [{ low: 0, mid: 1, high: 2 }, { low: 3, mid: 3, high: 3 }],
      code: { low: 3, mid: 3, high: 3 },
      method: 'poa-signal',
      claims_route: `/api/poa/signal/${authorityId}/claims`,
      note: '`accepted: true` is admission staging and settles nothing; the number that bites is '
        + '`latest_height` off GET /status AFTER finalization',
    },
  });

  test('the page BUILDS the claim off the served settlement and submits it through the extension', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);
    const commitment = 'c7'.repeat(32);

    await page.evaluate(([authorityId, commitmentHex, document]) => {
      const w = window as unknown as Record<string, any>;
      w.__settle = undefined;
      // The REAL parser and the REAL settle caller, both off disk.
      const session = w.__judged.parseSessionDocument(document, { authorityId, commitment: commitmentHex });
      // ⚑ What the page hands the extension, recorded before it goes — so the
      // assertion below is about the bytes that actually crossed the seam.
      w.__claimSent = w.__judged.settlementClaim(session.settlement);
      w.__judged
        .settleJudgedRun({ provider: w.dregg, session, deadlineMs: 1, pollMs: 1 })
        .then((r: unknown) => { w.__settle = r; })
        .catch((e: Error) => { w.__settle = { state: 'threw', reason: String(e && e.message) }; });
    }, [AUTHORITY, commitment, solvedDocument(AUTHORITY, commitment, 'd4'.repeat(32))] as const);

    await approveIfPrompted(context, 15000);
    await page.waitForFunction(() => (window as any).__settle !== undefined, null, { timeout: 40000 });
    const settle = await page.evaluate(() => (window as any).__settle as Record<string, unknown>);
    const sent = await page.evaluate(() => (window as any).__claimSent as Record<string, unknown>);

    // ⚑ THE PAGE'S WHOLE CONTRIBUTION, and it is exactly three keys off the
    // document the node served. No authority, no destination, no reward, no memo,
    // no nonce, no cell, no signature — those are the extension's, and a page
    // that offered them would be authoring custody.
    expect(Object.keys(sent).sort()).toEqual(['missionId', 'schema', 'transcript']);
    expect(sent.schema).toBe(CLAIM_SCHEMA);
    expect(sent.missionId).toBe(MISSION_ID);
    // The WHOLE run in order, not the solving code alone.
    expect(sent.transcript).toEqual([[0, 1, 2], [3, 3, 3]]);

    // ⚑ AND THE EXACT STOP, 2026-08-09. The claim reached the extension, passed
    // the origin gate, the parse, the wasm carrier, custody AND THE CELL
    // DERIVATION — the wall this test used to end on — and now dies asking the
    // pinned node. That is a PAGE → EXTENSION run that goes as far as a browser
    // can take it: everything on this side of the network works.
    //
    // The node was still never asked to SETTLE anything, and this file does not
    // pretend it was. `PoA Signal authority is unreachable: HTTP 401:` is the
    // beta curtain refusing at the reverse proxy, measured today.
    expect(settle.state, JSON.stringify(settle)).toBe('refused');
    expect(String(settle.reason), JSON.stringify(settle)).not.toContain(
      "Could not derive the active player's canonical cell",
    );
    expect(String(settle.reason), JSON.stringify(settle)).not.toContain(
      'installed dregg WASM does not include the PoA Signal carrier',
    );
    // The refusal a player sees names a NODE fact. Same reasoning as the pole
    // above: the exact HTTP code is today's deployment and is not pinned here.
    expect(String(settle.reason), JSON.stringify(settle)).toContain('PoA Signal authority');
    await page.close();
  });

  test('⚑ a code the player did not play is refused BY NAME, before any provider call', async ({ context }) => {
    const page = await openJudgedPage(context, BETA);
    const commitment = 'c7'.repeat(32);
    const popups: string[] = [];
    context.on('page', (p) => popups.push(p.url()));

    const outcome = await page.evaluate(([authorityId, commitmentHex, document]) => {
      const w = window as unknown as Record<string, any>;
      // A settlement naming a code this transcript never contains — the exact
      // shape a page would send if it wanted to claim a win it did not earn.
      const forged = JSON.parse(JSON.stringify(document));
      forged.settlement.transcript = [{ low: 5, mid: 5, high: 5 }, { low: 5, mid: 5, high: 5 }];
      forged.settlement.code = { low: 5, mid: 5, high: 5 };
      try {
        w.__judged.parseSessionDocument(forged, { authorityId, commitment: commitmentHex });
        return { refused: false, code: '', message: '' };
      } catch (e: any) {
        return { refused: true, code: String(e && e.code), message: String(e && e.message) };
      }
    }, [AUTHORITY, commitment, solvedDocument(AUTHORITY, commitment, 'd4'.repeat(32))] as const);

    // ⚑ REFUSED AT THE DOCUMENT, by name, so no claim can be built from it at
    // all. This is stronger than validating a claim: `settleJudgedRun` has no
    // transcript parameter, so the only way to name rounds is to forge the
    // SESSION — and the session is what refuses.
    expect(outcome.refused, 'a settlement naming unplayed rounds must be refused').toBe(true);
    expect(outcome.code).toBe('session-settlement');
    expect(outcome.message).toContain('not the round that was played');
    // And it never got as far as asking custody for anything.
    expect(popups.filter((u) => u.includes('.html'))).toHaveLength(0);
    await page.close();
  });
});
