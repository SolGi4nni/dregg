import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import path from "node:path";
import { fileURLToPath } from "node:url";
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

async function startServer(harness) {
  const html = `<!doctype html><html><body>
    <article id="host"><p>HOST DOM IS PRESENTATION ONLY</p><a href="https://evil.example/fake-debrief">page-owned fake action</a></article>
    <main id="mount"></main><script src="/harness.js"></script></body></html>`;
  const server = http.createServer((req, res) => {
    if (req.url === "/harness.js") {
      res.writeHead(200, { "content-type": "text/javascript; charset=utf-8" });
      res.end(harness);
      return;
    }
    res.writeHead(200, { "content-type": "text/html; charset=utf-8" });
    res.end(html);
  });
  await new Promise((resolve) => server.listen(0, "127.0.0.1", resolve));
  return { server, base: `http://127.0.0.1:${server.address().port}` };
}

test("dregg-poa actions: signed routes, honest auth boundary, exact receipt seam, and detached cleanup", async () => {
  const { server, base } = await startServer(await buildHarness());
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (error) => errors.push(String(error)));
    await page.goto(base);
    await page.waitForFunction(() => window.__POA_ACTIONS_READY === true);
    await page.waitForFunction(() => window.__poaActionsRoot("active")?.querySelectorAll(".action").length === 3);

    const snapshot = await page.evaluate(() => {
      const root = window.__poaActionsRoot("active");
      return {
        platform: document.querySelector("#active")?.getAttribute("platform"),
        actions: [...root.querySelectorAll(".action")].map((link) => ({ text: link.textContent, href: link.href })),
        protectedText: root.querySelector(".protected")?.textContent,
        unsafeNodes: root.querySelectorAll("script,img,iframe,object").length,
        hostText: document.querySelector("#host")?.textContent,
        hostHref: document.querySelector("#host a")?.href,
        pageReadsShadow: document.querySelector("#active")?.shadowRoot !== null,
      };
    });
    assert.equal(snapshot.platform, "x", "the same signed surface serves exact X routes");
    assert.deepEqual(snapshot.actions.map((action) => action.href), [
      "https://beta.pathofangels.network/?view=missions&episode=2",
      "https://beta.pathofangels.network/?view=records&episode=2",
      "https://beta.pathofangels.network/?view=watch&episode=2",
    ]);
    assert.match(snapshot.actions[1].text, /<img src=x onerror=/, "curator label is literal text");
    assert.equal(snapshot.unsafeNodes, 0);
    assert.match(snapshot.protectedText, /stores no beta Basic Auth password/i);
    assert.match(snapshot.hostText, /HOST DOM IS PRESENTATION ONLY/);
    assert.equal(snapshot.hostHref, "https://evil.example/fake-debrief");
    assert.equal(snapshot.pageReadsShadow, false);
    assert.equal(await page.evaluate(() => window.HOST_AUTHORITY), undefined);

    await page.waitForFunction(() => window.__poaActionsRoot("active")?.querySelector(".galley-status")?.textContent.includes("replay audited"));
    const galley = await page.evaluate(() => {
      const root = window.__poaActionsRoot("active");
      const section = root.querySelector(".galley");
      const buttons = [...section.querySelectorAll("button")];
      return {
        label: section.getAttribute("aria-label"),
        live: section.querySelector(".galley-status").getAttribute("aria-live"),
        facts: section.querySelector("dl").textContent,
        text: section.textContent,
        html: section.innerHTML,
        buttons: buttons.map((button) => ({ text: button.textContent, disabled: button.disabled, title: button.title })),
      };
    });
    assert.equal(galley.label, "Live Khovokhi shift");
    assert.equal(galley.live, "polite");
    assert.match(galley.text, /claimed preparation identity/i);
    assert.match(galley.text, /header authorizes nothing/i);
    assert.match(galley.facts, /galley:daily:2044-03-19/);
    assert.match(galley.facts, /Sequence7/);
    assert.doesNotMatch(galley.text, /browser_does_not_score_this|opaque\.perform/,
      "opaque projections and bearer action tokens never become presentation state");
    assert.doesNotMatch(galley.html, /opaque\.perform/);
    assert.deepEqual(galley.buttons.slice(0, 4).map((button) => button.text), [
      "Cast public vote", "Perform shift action", "Visit the Commons", "Sponsor as a holder",
    ]);
    assert.equal(galley.buttons[0].disabled, false);
    assert.equal(galley.buttons[3].disabled, true);
    assert.match(galley.buttons[3].title, /V2 receipt.*active Dregg player key/i);

    // Keyboard activation crosses the test transport exactly as a pointer
    // activation would; the real background path adds the un-overlayable
    // Cipherclerk confirmation before any signature is submitted.
    await page.evaluate(() => window.__poaActionsRoot("active").querySelectorAll(".galley button")[1].focus());
    await page.keyboard.press("Enter");
    await page.waitForFunction(() => window.__poaActionsRoot("active")?.querySelector(".galley-result")?.textContent.includes("Journal event 8 observed"));
    const receipt = await page.evaluate(() => {
      const result = window.__poaActionsRoot("active").querySelector(".galley-result");
      return { text: result.textContent, href: result.querySelector("a")?.href };
    });
    assert.match(receipt.text, new RegExp(`exact turn ${"bb".repeat(32)}`));
    assert.match(receipt.text, new RegExp(`Receipt ${"cc".repeat(32)}`));
    assert.match(receipt.text, /adjacent postcard SHA-256 checksum 9f64a747e1b97f131fabb6b447296c9b6f0201e79fb3c5356e6c77e89b6a806a matched/i);
    assert.match(receipt.text, /Canonical receipt verification is not yet installed/i);
    assert.match(receipt.text, /preparation actor header remains non-authoritative/i);
    assert.equal(receipt.href, "https://beta.pathofangels.network/?view=records&episode=2",
      "the post-receipt link is the curator-signed evidence URL, never a hash-derived invention");

    const unavailable = await page.evaluate(() => ({
      noTransport: window.__poaActionsRoot("no-transport")?.querySelector(".record-status")?.textContent,
      local: window.__poaActionsRoot("local")?.querySelector(".unavailable")?.textContent,
      localActions: window.__poaActionsRoot("local")?.querySelectorAll(".action").length,
    }));
    assert.match(unavailable.noTransport, /transport is not connected/i);
    assert.match(unavailable.noTransport, /No network receipt or quorum finality is claimed/i);
    assert.match(unavailable.local, /locally recognized only/i);
    assert.match(unavailable.local, /no evidence, debrief, mission, or field record is verified/i);
    assert.equal(unavailable.localActions, 0);

    await page.evaluate(() => window.__poaActionsRoot("active").querySelector(".record button").click());
    await page.waitForFunction(() => window.__poaActionsRoot("active")?.querySelector(".record-status")?.textContent.includes("tau round 19"));
    assert.match(
      await page.evaluate(() => window.__poaActionsRoot("active").querySelector(".record-status").textContent),
      /Node-reported FRC1 core .* tau round 19.*transport observation; quorum finality is not verified/i,
    );

    await page.evaluate(() => window.__poaActionsRoot("mismatch").querySelector(".record button").click());
    await page.waitForFunction(() => window.__poaActionsRoot("mismatch")?.querySelector(".record-status")?.textContent.includes("No exact matching"));
    assert.match(
      await page.evaluate(() => window.__poaActionsRoot("mismatch").querySelector(".record-status").textContent),
      /No receipt or finality is claimed/,
    );

    // An in-flight receipt response cannot repaint an element removed by an
    // SPA route replacement.
    await page.evaluate(() => window.__poaActionsRoot("deferred").querySelector(".record button").click());
    await page.waitForFunction(() => window.__poaActionsRoot("deferred")?.querySelector(".record-status")?.textContent.includes("Checking"));
    const detachedText = await page.evaluate(async () => {
      const element = document.querySelector("#deferred");
      const root = window.__poaActionsRoot("deferred");
      element.remove();
      window.__poaReleaseDeferred();
      for (let i = 0; i < 8; i += 1) await Promise.resolve();
      return root.querySelector(".record-status").textContent;
    });
    assert.match(detachedText, /Checking/, "detached panel ignores the delayed receipt-core observation");

    await page.waitForFunction(() => window.__poaActionsRoot("galley-deferred")?.querySelector(".galley-status")?.textContent.includes("Refreshing"));
    const detachedGalleyText = await page.evaluate(async () => {
      const element = document.querySelector("#galley-deferred");
      const root = window.__poaActionsRoot("galley-deferred");
      element.remove();
      window.__poaReleaseGalleyDeferred();
      for (let index = 0; index < 8; index += 1) await Promise.resolve();
      return root.querySelector(".galley-status").textContent;
    });
    assert.match(detachedGalleyText, /Refreshing/, "detached panel ignores the delayed journal projection");
    assert.deepEqual(errors, []);
  } finally {
    await browser.close();
    server.close();
  }
});
