import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

async function buildHarness() {
  const out = await esbuild.build({
    entryPoints: [path.join(__dirname, "harness.ts")],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2022"],
    write: false,
  });
  return out.outputFiles[0].text;
}

async function startServer(harnessJs) {
  const fixture = await readFile(path.join(__dirname, "fixture.html"), "utf8");
  const server = http.createServer((req, res) => {
    const url = req.url.split("?")[0];
    if (url === "/" || url === "/fixture.html") {
      res.writeHead(200, { "content-type": "text/html; charset=utf-8" });
      return res.end(fixture);
    }
    if (url === "/harness.js") {
      res.writeHead(200, { "content-type": "text/javascript; charset=utf-8" });
      return res.end(harnessJs);
    }
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  return { server, base: `http://127.0.0.1:${server.address().port}` };
}

const SNAPSHOT = `
window.__poaSnap = function () {
  const elements = [...document.querySelectorAll('dregg-poa')];
  return elements.map((el) => {
    const root = window.__dreggPoARoots && window.__dreggPoARoots.get(el);
    const descent = root && root.querySelector('dregg-descent');
    return {
      platform: el.getAttribute('platform'),
      contextId: el.getAttribute('context-id'),
      videoId: el.getAttribute('video-id'),
      postId: el.getAttribute('post-id'),
      trust: el.getAttribute('trust'),
      recognized: el.hasAttribute('recognized'),
      verified: el.hasAttribute('verified'),
      signed: el.hasAttribute('manifest-signed'),
      contentEpoch: el.getAttribute('content-epoch'),
      manifestCounter: el.getAttribute('manifest-counter'),
      expiresAt: el.getAttribute('expires-at'),
      error: el.hasAttribute('error'),
      pageSeesShadow: el.shadowRoot !== null,
      title: root ? root.querySelector('.title')?.textContent : null,
      dispatch: root ? root.querySelector('.dispatch')?.textContent : null,
      epochText: root ? root.querySelector('.epoch')?.textContent : null,
      badge: root ? root.querySelector('.badge')?.textContent : null,
      betaHref: root ? root.querySelector('.links a')?.href : null,
      fallbackHref: el.querySelector('a[data-poa-fallback]')?.href || null,
      descentSrc: descent?.getAttribute('src') || null,
      descentVerified: descent?.hasAttribute('verified') || false,
      pageSeesDescentShadow: descent ? descent.shadowRoot !== null : null,
      unsafeNodeCount: root ? root.querySelectorAll('script,img,iframe,object').length : null,
      followsSourcePost: el.previousElementSibling?.hasAttribute('data-x-source-post') || false,
    };
  });
};
`;

test("dregg-poa: opt-in + signed context + closed shadow + engine route + SPA replacement + fail-closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (error) => errors.push(String(error)));
    await page.addInitScript(SNAPSHOT);
    await page.goto(`${base}/fixture.html`);
    await page.waitForFunction(() => window.__DREGG_READY === true || window.__DREGG_ERROR, null, { timeout: 30000 });
    assert.equal(await page.evaluate(() => window.__DREGG_ERROR || null), null);
    assert.equal(await page.evaluate(() => window.__POA_DENIED_COUNT), 0, "denied origin mounts nothing");

    await page.waitForFunction(() => document.querySelector("dregg-poa[verified]"), null, { timeout: 10000 });
    await page.waitForFunction(() => {
      const poa = document.querySelector("dregg-poa");
      const root = window.__dreggPoARoots?.get(poa);
      return root?.querySelector("dregg-descent")?.hasAttribute("verified");
    });
    let [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.pageSeesShadow, false, "page cannot read PoA closed shadow");
    assert.equal(snap.pageSeesDescentShadow, false, "nested game also keeps its closed shadow");
    assert.equal(snap.verified, true, "curator-signed manifest is verified");
    assert.equal(snap.recognized, true);
    assert.equal(snap.signed, true, "signed manifest trust is reflected");
    assert.equal(snap.trust, "extension");
    assert.equal(snap.platform, "youtube");
    assert.equal(snap.contextId, "AbCdEfGhI01");
    assert.equal(snap.contentEpoch, "1");
    assert.equal(snap.manifestCounter, "1");
    assert.equal(snap.expiresAt, "1800003600");
    assert.match(snap.epochText, /manifest revision 1\.1/i);
    assert.match(snap.title, /Field Dispatch 1/);
    assert.match(snap.dispatch, /Deck 401/);
    assert.match(snap.badge, /curator manifest verified/i);
    assert.equal(snap.descentSrc, "dregg://descent/b3_de5ce0", "mission routes to existing Descent engine");
    assert.equal(snap.descentVerified, true);
    assert.match(snap.betaHref, /^https:\/\/beta\.pathofangels\.network\//);
    assert.match(snap.fallbackHref, /^https:\/\/beta\.pathofangels\.network\//, "light-DOM beta fallback remains");
    assert.equal(await page.evaluate(() => window.__poaLookupCount()), 1, "primed response avoids a second node lookup");

    // A higher route-free signed revision revokes an already-mounted game on
    // focus refresh. Hostile markup remains literal text under page CSP.
    await page.evaluate(() => window.__poaRevokeA());
    await page.waitForFunction(() => document.querySelector('dregg-poa[manifest-counter="2"]'));
    [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.verified, true, "route-free revocation is itself curator-verified");
    assert.equal(snap.descentSrc, null, "higher route-free revision removes the mounted game");
    assert.match(snap.epochText, /manifest revision 1\.2/i);
    assert.match(snap.dispatch, /<img src=x onerror=/, "signed dispatch markup is shown literally");
    assert.equal(snap.unsafeNodeCount, 0, "signed content cannot inject script/image/frame/object DOM");
    assert.equal(await page.evaluate(() => window.__POA_XSS), undefined, "no inline handler executed under CSP/runtime");

    // A stale signed route fetched later cannot restore the revoked game. The
    // current verified panel remains mounted until its signed expiry.
    const beforeRollback = await page.evaluate(() => window.__poaCompletedLookupCount());
    await page.evaluate(() => window.__poaRollbackA());
    await page.waitForFunction((n) => window.__poaCompletedLookupCount() > n, beforeRollback);
    await page.waitForTimeout(50);
    [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.manifestCounter, "2");
    assert.equal(snap.descentSrc, null, "rollback cannot resurrect the revoked route");

    // YouTube tears down sidebars during SPA navigation. Same-video replacement
    // remounts from the accepted model without duplicating or re-fetching.
    const beforeRemount = await page.evaluate(() => window.__poaLookupCount());
    await page.evaluate(() => window.__poaRemoveMounted());
    await page.waitForFunction(() => document.querySelectorAll("dregg-poa").length === 1);
    assert.equal(await page.evaluate(() => window.__poaLookupCount()), beforeRemount);

    // Crossing expiresAt unmounts synchronously before a slow/offline transport
    // is allowed to answer. Mutation-driven duplicate lookups are held too: no
    // signed shell or nested game survives anywhere in the request window.
    await page.evaluate(() => window.__poaExpireAOfflineHeld());
    await page.waitForFunction(() => window.__poaDeferredCount() > 0);
    assert.equal(await page.evaluate(() => document.querySelectorAll("dregg-poa").length), 0,
      "expired signed panel is absent while refresh transport is stalled");
    assert.equal(await page.evaluate(() => window.__poaSnap().length), 0,
      "expired nested game has no stale display window");
    assert.equal(await page.evaluate(() => window.__poaReleaseDeferredAndFlush()), 0);

    // Restore the still-valid revision, then hold its next valid response until
    // after its lease expires. The content side rejects it on arrival instead
    // of mounting it for even the zero-delay timer window.
    await page.evaluate(() => window.__poaResetClock());
    await page.evaluate(() => window.__poaRestoreRevokedA());
    await page.waitForFunction(() => document.querySelector('dregg-poa[manifest-counter="2"]'));
    await page.evaluate(() => window.__poaHoldValidA());
    await page.waitForFunction(() => window.__poaDeferredCount() > 0);
    await page.evaluate(() => window.__poaAdvancePastAExpiry());
    assert.equal(await page.evaluate(() => window.__poaReleaseDeferredAndFlush()), 0,
      "signed response that expires in flight is never mounted on arrival");
    await page.evaluate(() => window.__poaResetClock());

    const videos = await page.evaluate(() => window.__POA_VIDEOS);
    await page.evaluate((id) => window.__poaSetVideo(id), videos.VIDEO_B);
    await page.waitForFunction((id) => document.querySelector(`dregg-poa[video-id="${id}"]`), videos.VIDEO_B);
    assert.equal(await page.evaluate(() => document.querySelectorAll("dregg-poa").length), 1, "SPA keeps exactly one companion");
    [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.signed, true);
    assert.match(snap.title, /Field Dispatch 2/);
    assert.equal(snap.descentSrc, null, "manifest without a game does not fabricate one");

    // A correctly signed manifest for a DIFFERENT URL must fail closed: no mount.
    await page.evaluate((id) => window.__poaSetVideo(id), videos.VIDEO_MISMATCH);
    await page.waitForFunction(() => document.querySelectorAll("dregg-poa").length === 0);

    // Exact local video allowlist recognizes only a safe, game-free shell.
    await page.evaluate((id) => window.__poaSetVideo(id), videos.VIDEO_LOCAL);
    await page.waitForFunction((id) => document.querySelector(`dregg-poa[video-id="${id}"]`), videos.VIDEO_LOCAL);
    [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.verified, false, "local allowlist recognizes but does not verify");
    assert.equal(snap.recognized, true);
    assert.equal(snap.trust, "local");
    assert.equal(snap.signed, false);
    assert.match(snap.badge, /locally recognized · not verified/i);
    assert.equal(snap.descentSrc, null, "local allowlist cannot attach game semantics");
    assert.match(snap.fallbackHref, /^https:\/\/beta\.pathofangels\.network\//, "local shell keeps beta fallback");

    // The same verified lifecycle serves an exact browser-authenticated X post.
    // X mounts alongside the matching article/card target, never by rewriting
    // its page-owned prose, and leaving the status route removes it SPA-safely.
    // Actual pushState: no synthetic popstate and no DOM mutation. The bounded
    // URL watcher removes the prior panel before the held X lookup can answer.
    await page.evaluate((id) => window.__poaPushXPostHeld(id), videos.X_POST);
    await page.waitForFunction(() => window.__poaDeferredCount() > 0);
    assert.equal(await page.evaluate(() => document.querySelectorAll("dregg-poa").length), 0,
      "the prior YouTube panel is removed while the X SPA lookup is in flight");

    // replaceState away from A in the same task that releases A's delayed
    // response. The post-await live-context check rejects A before any mount,
    // even before the watcher/navigation event gets another turn.
    assert.equal(await page.evaluate(() => window.__poaReplaceNoContextAndRelease()), 0,
      "delayed X response cannot mount after a silent same-document route change");

    await page.evaluate((id) => window.__poaPushXPost(id), videos.X_POST);
    await page.waitForFunction((id) => document.querySelector(`dregg-poa[post-id="${id}"][verified]`), videos.X_POST);
    await page.waitForFunction(() => {
      const poa = document.querySelector('dregg-poa[platform="x"]');
      const root = window.__dreggPoARoots?.get(poa);
      return root?.querySelector("dregg-descent")?.hasAttribute("verified");
    });
    [snap] = await page.evaluate(() => window.__poaSnap());
    assert.equal(snap.platform, "x");
    assert.equal(snap.contextId, videos.X_POST);
    assert.equal(snap.postId, videos.X_POST);
    assert.equal(snap.videoId, null);
    assert.equal(snap.followsSourcePost, true, "X panel is inserted beside, not inside/replacing, the source post target");
    assert.match(await page.locator('[data-x-source-post] p').textContent(), /remains page-owned and untouched/);
    assert.equal(snap.descentSrc, "dregg://descent/b3_de5ce0");
    assert.match(snap.dispatch, /<img src=x onerror=/, "X dispatch markup is text, not HTML");
    assert.equal(snap.unsafeNodeCount, 0);
    assert.equal(await page.evaluate(() => window.__POA_X_XSS), undefined);

    const beforeXRemount = await page.evaluate(() => window.__poaLookupCount());
    await page.evaluate(() => window.__poaRemoveMounted());
    await page.waitForFunction((id) => document.querySelector(`dregg-poa[post-id="${id}"]`), videos.X_POST);
    assert.equal(await page.evaluate(() => window.__poaLookupCount()), beforeXRemount,
      "X card teardown remounts the accepted signed model without a second lookup");

    // Actual replaceState with no DOM mutation/popstate removes the accepted X
    // panel through same-document URL observation.
    await page.evaluate(() => window.__poaReplaceNoContext());
    await page.waitForFunction(() => document.querySelectorAll("dregg-poa").length === 0);

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
