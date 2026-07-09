// Fixture test for the quiet-upgrade loop (DREGG-QUIET-UPGRADE.md §9 steps 1–3).
//
// Serves a static page with plaintext dregg-poll references, loads it in a real
// (headless) Chromium via Playwright, and asserts the full loop:
//   detector upgrades → element renders (closed shadow) → click casts a REAL
//   verified turn → tally repaints → [verified] → double-vote is REFUSED and
//   surfaced; and a malformed addr FAILS CLOSED (original link + warning, no
//   render).  The engine runs the REAL wasm PollWorld; the element uses its real
//   closed shadow + message transport.  Only the transport hop + consent are
//   shimmed in-page (see harness.ts).
//
// Run:  node tests/quiet-upgrade/run.mjs      (or: node --test tests/quiet-upgrade/run.mjs)

import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const EXT_ROOT = path.resolve(__dirname, "..", "..");

const MIME = {
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
  ".html": "text/html; charset=utf-8",
};

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
  const glue = await readFile(path.join(EXT_ROOT, "dregg_wasm.js"), "utf8");
  const wasm = await readFile(path.join(EXT_ROOT, "dregg_wasm_bg.wasm"));

  const server = http.createServer((req, res) => {
    const url = req.url.split("?")[0];
    const send = (body, type) => {
      res.writeHead(200, { "content-type": type });
      res.end(body);
    };
    if (url === "/" || url === "/fixture.html") return send(fixture, MIME[".html"]);
    if (url === "/harness.js") return send(harnessJs, MIME[".js"]);
    if (url === "/dregg_wasm.js") return send(glue, MIME[".js"]);
    if (url === "/dregg_wasm_bg.wasm") return send(wasm, MIME[".wasm"]);
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const { port } = server.address();
  return { server, base: `http://127.0.0.1:${port}` };
}

test("quiet upgrade: upgrade → vote → verify → double-vote refused; and fail-closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));
    await page.goto(`${base}/fixture.html`);

    // Boot: wasm loaded, engine + detector wired.
    await page.waitForFunction(() => window.__DREGG_READY === true || window.__DREGG_ERROR, null, {
      timeout: 30000,
    });
    const bootErr = await page.evaluate(() => window.__DREGG_ERROR || null);
    assert.equal(bootErr, null, `harness boot error: ${bootErr}`);

    // The detector upgraded every reference (3 valid + 1 malformed).
    await page.waitForSelector("dregg-poll", { timeout: 10000 });
    // Wait until each element has settled its trust state (verified or error).
    await page.waitForFunction(
      () => {
        const els = [...document.querySelectorAll("dregg-poll")];
        return els.length === 4 && els.every((el) => el.hasAttribute("verified") || el.hasAttribute("error"));
      },
      null,
      { timeout: 10000 },
    );

    const snapshot = () =>
      page.evaluate(() => {
        const roots = window.__dreggPollRoots;
        return [...document.querySelectorAll("dregg-poll")].map((el) => {
          const root = roots && roots.get(el);
          return {
            src: el.getAttribute("src"),
            trust: el.getAttribute("trust"),
            verified: el.hasAttribute("verified"),
            error: el.hasAttribute("error"),
            votes: el.getAttribute("votes"),
            voteRefused: el.hasAttribute("vote-refused"),
            pageSeesShadow: el.shadowRoot !== null, // closed ⇒ always false
            hasFallbackLink: !!el.querySelector('a[href^="https://dregg.net/d/poll/"]'),
            hasWarning: !!el.querySelector(".dregg-fallback-warning"),
            live: root ? (root.querySelector(".live")?.textContent || "").trim() : null,
            badge: root ? (root.querySelector(".badge")?.textContent || "").trim() : null,
            buttons: root ? root.querySelectorAll("button[data-turn]").length : null,
            note: root ? (root.querySelector(".note")?.textContent || "").trim() : null,
          };
        });
      });

    const bySrc = (snap, src) => snap.find((s) => s.src === src);

    let snap = await snapshot();
    assert.equal(snap.length, 4, "four references upgraded");

    // ── The SPLIT: the page can never see inside any thin view (closed shadow).
    for (const s of snap) assert.equal(s.pageSeesShadow, false, `${s.src}: closed shadow hides render from page`);

    // ── The three valid polls are VERIFIED by the extension engine.
    const prose = bySrc(snap, "dregg://poll/b3_a1a1a1");
    const mirror = bySrc(snap, "dregg://poll/b3_b2b2b2");
    const tco = bySrc(snap, "dregg://poll/b3_c3c3c3");
    for (const [name, s] of [["prose", prose], ["mirror", mirror], ["tco", tco]]) {
      assert.ok(s, `${name} element exists`);
      assert.equal(s.verified, true, `${name}: [verified] reflected`);
      assert.equal(s.error, false, `${name}: no [error]`);
      assert.equal(s.trust, "extension", `${name}: trust=extension`);
      assert.match(s.badge, /verified by your cipherclerk/, `${name}: honest badge`);
      assert.ok(s.buttons >= 2, `${name}: vote affordances rendered in shadow`);
      assert.ok(s.hasFallbackLink, `${name}: light-DOM fallback link preserved`);
    }

    // ── The malformed addr FAILS CLOSED: no render, original link + warning.
    const bad = bySrc(snap, "dregg://poll/notahash");
    assert.ok(bad, "malformed reference still upgraded to an element");
    assert.equal(bad.verified, false, "bad: not verified");
    assert.equal(bad.error, true, "bad: [error] set");
    assert.equal(bad.trust, "none", "bad: trust=none");
    assert.equal(bad.live, null, "bad: NOTHING rendered (no shadow)");
    assert.ok(bad.hasFallbackLink, "bad: original link kept as fallback");
    assert.ok(bad.hasWarning, "bad: visible warning shown");

    // ── Surrounding prose preserved (respectful replacement).
    const proseText = await page.evaluate(() => document.getElementById("prose").textContent);
    assert.match(proseText, /Should we ship it\?/);
    assert.match(proseText, /thanks!/);

    // ── Idempotency: a mutation-driven re-scan does not duplicate.
    await page.evaluate(() => {
      document.getElementById("prose").appendChild(document.createTextNode(" (edited)"));
    });
    await page.waitForTimeout(200);
    const countAfter = await page.evaluate(() => document.querySelectorAll("dregg-poll").length);
    assert.equal(countAfter, 4, "no duplicate upgrade on re-scan");

    const liveBefore = prose.live;

    // ── Click a choice → a REAL verified cast → tally repaints, still verified.
    await page.evaluate(() => {
      const el = [...document.querySelectorAll("dregg-poll")].find(
        (e) => e.getAttribute("src") === "dregg://poll/b3_a1a1a1",
      );
      window.__dreggPollRoots.get(el).querySelector('button[data-arg="0"]').click();
    });
    await page.waitForFunction(
      () => {
        const el = [...document.querySelectorAll("dregg-poll")].find(
          (e) => e.getAttribute("src") === "dregg://poll/b3_a1a1a1",
        );
        return el.getAttribute("votes") === "1";
      },
      null,
      { timeout: 15000 },
    );
    snap = await snapshot();
    const prose2 = bySrc(snap, "dregg://poll/b3_a1a1a1");
    assert.equal(prose2.verified, true, "still verified after cast");
    assert.equal(prose2.voteRefused, false, "first cast not refused");
    assert.notEqual(prose2.live, liveBefore, "tally repainted after cast");

    // ── Double vote (same viewer ballot) is REFUSED and surfaced.
    await page.evaluate(() => {
      const el = [...document.querySelectorAll("dregg-poll")].find(
        (e) => e.getAttribute("src") === "dregg://poll/b3_a1a1a1",
      );
      window.__dreggPollRoots.get(el).querySelector('button[data-arg="0"]').click();
    });
    await page.waitForFunction(
      () => {
        const el = [...document.querySelectorAll("dregg-poll")].find(
          (e) => e.getAttribute("src") === "dregg://poll/b3_a1a1a1",
        );
        return el.hasAttribute("vote-refused");
      },
      null,
      { timeout: 15000 },
    );
    snap = await snapshot();
    const prose3 = bySrc(snap, "dregg://poll/b3_a1a1a1");
    assert.equal(prose3.voteRefused, true, "double vote refused");
    assert.match(prose3.note, /refused/i, "refusal surfaced in the view");
    assert.equal(prose3.votes, "1", "tally unchanged by the refused double vote");
    assert.equal(prose3.verified, true, "still verified after refusal");

    // ── Consent is load-bearing: deny it → the cast is refused, no tally change.
    await page.evaluate(() => (window.__DREGG_CONSENT = false));
    await page.evaluate(() => {
      const el = [...document.querySelectorAll("dregg-poll")].find(
        (e) => e.getAttribute("src") === "dregg://poll/b3_b2b2b2",
      );
      window.__dreggPollRoots.get(el).querySelector('button[data-arg="0"]').click();
    });
    await page.waitForFunction(
      () => {
        const el = [...document.querySelectorAll("dregg-poll")].find(
          (e) => e.getAttribute("src") === "dregg://poll/b3_b2b2b2",
        );
        return el.hasAttribute("vote-refused");
      },
      null,
      { timeout: 15000 },
    );
    snap = await snapshot();
    const mirror2 = bySrc(snap, "dregg://poll/b3_b2b2b2");
    assert.match(mirror2.note, /consent denied/i, "denied consent surfaced");
    assert.equal(mirror2.votes, "0", "no tally change when consent denied");

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
  } finally {
    await browser.close();
    server.close();
  }
});
