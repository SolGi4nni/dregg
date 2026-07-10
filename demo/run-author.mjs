// THE DRIVEN RUN — the authoring surface, exercised end-to-end in headless Chromium.
//
// It loads /author, and asserts the whole compile loop:
//   1. the STARTER story compiles + mounts + plays (advance a choice → the receipt
//      count grows → verify() replays true);
//   2. a deliberately BROKEN scene → Play → a legible compile error is shown WITH a
//      line, NO world is mounted, and the previously mounted world is NOT kept;
//   3. a freshly-typed tiny VALID scene → Play → it compiles and plays + verifies.
// Then it captures a screenshot + a transcript.
//
//   node demo/run-author.mjs

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";
import { makeServer } from "./serve.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");
const OUT = path.join(__dirname, "run");

// A deliberately broken scene: it navigates to a passage that does not exist, so the
// wasm compiler fails closed with an "unknown passage `nowhere`" message the page can
// pin to the `-> nowhere` line.
const BROKEN = `---
id: broken
title: Broken
---

=== start

A door stands before you.

* [Open it]
  -> nowhere
`;

// A tiny, freshly-typed VALID scene: one choice, an effect, an ending.
const TINY = `---
id: tiny
title: A Tiny Tale
---

=== start

You stand at a fork in a bright wood.

* [Walk into the light]
  ~ brave = 1
  -> clearing

=== clearing

Sun on the grass. You made it. THE END.
`;

async function main() {
  await mkdir(OUT, { recursive: true });
  const { server, base } = await makeServer(0);
  const browser = await chromium.launch({ headless: true });
  const pageErrors = [];
  const T = [];
  try {
    const page = await browser.newPage({ viewport: { width: 1280, height: 1500 }, deviceScaleFactor: 2 });
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/author`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__authorReady === true, null, { timeout: 45000 });
    const bootErr = await page.evaluate(() => window.__authorError || null);
    if (bootErr) throw new Error(`the authoring page failed to boot: ${bootErr}`);

    // ── 1) THE STARTER compiles + mounts + verifies ──
    const s0 = await page.evaluate(() => window.__authorState());
    assert.equal(s0.mounted, true, "the starter story compiled + mounted at boot");
    assert.ok(s0.receipts >= 1, `the starter has a genesis receipt (got ${s0.receipts})`);
    assert.ok(s0.counts.passages >= 3, `the starter has multiple passages (got ${s0.counts.passages})`);
    const v0 = await page.evaluate(() => window.__authorVerify());
    assert.equal(v0.verified, true, "the starter replay-verifies at load");
    T.push(`STARTER   compiled · ${s0.counts.passages} passages, ${s0.counts.choices} choices · ${s0.receipts} receipt(s) · verify=${v0.verified}`);
    T.push(`          opening passage: "${s0.passage}"`);

    // ── advance a choice → receipts grow → verify still true ──
    const adv = await page.evaluate(() => window.__authorAdvance(0));
    assert.equal(adv.ok, true, `advancing a choice committed a verified turn (${JSON.stringify(adv)})`);
    assert.ok(adv.after > adv.before, `the receipt count grew on advance (${adv.before} → ${adv.after})`);
    assert.equal(adv.verified, true, "the chain still replay-verifies after the choice");
    T.push(`ADVANCE   chose a branch → receipts ${adv.before} → ${adv.after} · now at "${adv.passage}" · verify=${adv.verified}`);

    // ── 2) A BROKEN scene fails closed: a legible error, NO world mounted ──
    await page.evaluate((b) => window.__authorSetText(b), BROKEN);
    const broke = await page.evaluate(() => window.__authorPlay());
    assert.equal(broke.ok, false, "the broken scene did NOT compile");
    const sBroke = await page.evaluate(() => window.__authorState());
    assert.equal(sBroke.hasElement, false, "no world element is mounted after a compile failure (fail-closed)");
    assert.equal(sBroke.mounted, false, "the previous world was NOT silently kept behind the error");
    assert.ok(sBroke.error && /unknown/i.test(sBroke.error), `the error message is legible (got: ${sBroke.error})`);
    assert.ok(Number.isInteger(sBroke.errorLine) && sBroke.errorLine > 0, `the error is pinned to a line (got: ${sBroke.errorLine})`);
    const errText = await page.evaluate(() => (document.getElementById("error")?.textContent || "").trim());
    assert.ok(/fail-closed/i.test(errText), "the error panel says fail-closed");
    T.push(`BROKEN    Play → error shown, NO world mounted (fail-closed)`);
    T.push(`          line ${sBroke.errorLine}: ${sBroke.error}`);

    // ── 3) A freshly-typed VALID scene compiles + plays + verifies ──
    await page.evaluate((t) => window.__authorSetText(t), TINY);
    const fixed = await page.evaluate(() => window.__authorPlay());
    assert.equal(fixed.ok, true, `the typed valid scene compiled (${JSON.stringify(fixed)})`);
    const sFixed = await page.evaluate(() => window.__authorState());
    assert.equal(sFixed.mounted, true, "the typed scene mounted + verified");
    const vFixed = await page.evaluate(() => window.__authorVerify());
    assert.equal(vFixed.verified, true, "the typed scene replay-verifies");
    T.push(`TYPED     a fresh valid scene → compiled · ${sFixed.counts.passages} passages · ${sFixed.receipts} receipt(s) · verify=${vFixed.verified}`);
    // play it one step to show it is live
    const adv2 = await page.evaluate(() => window.__authorAdvance(0));
    assert.equal(adv2.ok, true, "the typed scene is playable");
    T.push(`          advanced → receipts ${adv2.before} → ${adv2.after} · at "${adv2.passage}" · verify=${adv2.verified}`);

    // ── CAPTURE ──
    await page.waitForTimeout(250);
    await page.screenshot({ path: path.join(OUT, "author.png"), fullPage: true });

    const transcript = [
      "AUTHOR — write a verifiable story, play it, verify it",
      "driven run · real wasm StoryWorld compiled from live editor text",
      "served at " + base + "/author",
      "=".repeat(64),
      "",
      ...T,
      "",
      "-".repeat(64),
      "the compile loop: ▶ Play → new StoryWorld(editorText).",
      "  · a good scene mounts the real <dregg-story> and plays as verified turns;",
      "  · a bad scene fails closed — a legible, line-pinned error, and NO world mounted.",
      "",
    ].join("\n");
    await writeFile(path.join(OUT, "author.txt"), transcript, "utf8");

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "author.png")}`);
    console.log(`  transcript → ${path.join(OUT, "author.txt")}\n`);
    console.log("  ✓ THE AUTHORING SURFACE RAN: live compile, play, verify; broken-scene fails closed.\n");
  } finally {
    await browser.close();
    server.close();
  }
}

main().catch((e) => {
  console.error("\n  ✗ RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
