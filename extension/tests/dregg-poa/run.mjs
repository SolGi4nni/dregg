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
      videoId: el.getAttribute('video-id'),
      trust: el.getAttribute('trust'),
      recognized: el.hasAttribute('recognized'),
      verified: el.hasAttribute('verified'),
      signed: el.hasAttribute('manifest-signed'),
      error: el.hasAttribute('error'),
      pageSeesShadow: el.shadowRoot !== null,
      title: root ? root.querySelector('.title')?.textContent : null,
      dispatch: root ? root.querySelector('.dispatch')?.textContent : null,
      badge: root ? root.querySelector('.badge')?.textContent : null,
      betaHref: root ? root.querySelector('.links a')?.href : null,
      fallbackHref: el.querySelector('a[data-poa-fallback]')?.href || null,
      descentSrc: descent?.getAttribute('src') || null,
      descentVerified: descent?.hasAttribute('verified') || false,
      pageSeesDescentShadow: descent ? descent.shadowRoot !== null : null,
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
    assert.match(snap.title, /Field Dispatch 1/);
    assert.match(snap.dispatch, /Deck 401/);
    assert.match(snap.badge, /curator manifest verified/i);
    assert.equal(snap.descentSrc, "dregg://descent/b3_de5ce0", "mission routes to existing Descent engine");
    assert.equal(snap.descentVerified, true);
    assert.match(snap.betaHref, /^https:\/\/beta\.pathofangels\.network\//);
    assert.match(snap.fallbackHref, /^https:\/\/beta\.pathofangels\.network\//, "light-DOM beta fallback remains");
    assert.equal(await page.evaluate(() => window.__poaLookupCount()), 1, "primed response avoids a second node lookup");

    // YouTube tears down sidebars during SPA navigation. Same-video replacement
    // remounts from the accepted model without duplicating or re-fetching.
    await page.evaluate(() => window.__poaRemoveMounted());
    await page.waitForFunction(() => document.querySelectorAll("dregg-poa").length === 1);
    assert.equal(await page.evaluate(() => window.__poaLookupCount()), 1);

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

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
