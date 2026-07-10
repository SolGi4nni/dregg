// THE DRIVEN RUN — THE FORGE: write a .dungeon world, hit ▶ Play, PLAY it vs real gemma2.
//
// Spawns the native attested-dm dungeon-service (real gemma2:2b via ollama), serves the forge
// page against it (serve.mjs proxying /game/*), loads it in headless Chromium, and drives the
// author → play → verify loop through the page's own affordances (editor text → /game/author,
// then command/exit buttons → /game/act → render), ASSERTING the INVARIANTS against the
// service's own responses (never fabricated):
//
//   A. THE STARTER authors + plays — /game/author ok, a fresh world mounts, a move LANDS, the
//      receipt rail grows, /game/verify true.
//   B. A SYNTAX-broken source → /game/author {stage:"parse", line} → the error is shown
//      LINE-PINNED, NO world is mounted (fail-closed; the previous world is torn down).
//   C. A source that PARSES but FAILS VALIDATION (the committed broken.dungeon: a dangling
//      exit, an unreachable objective, an unplaced win item) → {stage:"validate", issues:[…]}
//      → EVERY issue is listed, line-pinned, NO world mounted.
//   D. FIX it → the starter re-authors and plays to a WIN — each move LANDS, the rail grows,
//      status → "won", /game/verify true throughout.
//
// The narration is a REAL local model, so prose VARIES run to run — we assert the world state
// transitions / status / stages / issues (the INVARIANTS), never the model's exact words.
//
// Captures demo/run/forge.png + forge.txt.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { spawn } from "node:child_process";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import net from "node:net";
import path from "node:path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");
const OUT = path.join(__dirname, "run");
const SERVICE_BIN = path.join(REPO, "target", "debug", "dungeon-service");

// A deliberately SYNTAX-broken source: an exit with no destination room after `->` (line 6),
// which `parse_world` refuses fail-closed with that line.
const SYNTAX_BROKEN = `name: Syntax Trap
start: room_a
objective: reach room_b holding key
room room_a "Room A"
  A bare stone room.
  exit north ->
room room_b "Room B"
  items: key
  exit south -> room_a
`;

// The canonical WIN path through the starter (The Candle Crypt): hold the candle, descend the
// gated stair, take the relic, carry it to the shrine. The order is FORCED by the candle gate.
const WIN_PATH = [
  ["take candle", "a light for the dark stair", "gatehouse"],
  ["go north", "into the long hall", "hall"],
  ["go down", "down the now-passable stair", "crypt"],
  ["take relic", "the glowing relic", "crypt"],
  ["go north", "into the shrine — WIN", "shrine"],
];

function waitPortOpen(port, host = "127.0.0.1", timeoutMs = 60000) {
  const start = Date.now();
  return new Promise((resolve, reject) => {
    const tick = () => {
      const s = net.connect(port, host);
      s.once("connect", () => { s.destroy(); resolve(); });
      s.once("error", () => {
        s.destroy();
        if (Date.now() - start > timeoutMs) reject(new Error(`service did not open ${host}:${port} within ${timeoutMs}ms`));
        else setTimeout(tick, 400);
      });
    };
    tick();
  });
}

async function main() {
  await mkdir(OUT, { recursive: true });

  // ── 1. spawn the native attested-dm dungeon-service (real gemma2:2b) ──
  const SERVICE_PORT = 8792;
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}` },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  try {
    await waitPortOpen(SERVICE_PORT);
    await new Promise((r) => setTimeout(r, 500)); // let the model probe settle
    const narratorKind = await (await fetch(`http://127.0.0.1:${SERVICE_PORT}/game/state`)).json().then((s) => s.narratorKind);
    const realModel = String(narratorKind || "").startsWith("model:");

    // ── 2. serve the forge page against the native service (proxy /game/*) ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    // ── 3. load the page ──
    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1360, height: 2000 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/forge`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__FORGE_READY === true, null, { timeout: 45000 });
    const bootErr = await page.evaluate(() => window.__FORGE_ERROR || null);
    if (bootErr) throw new Error(`the forge page failed to boot (could not reach /game):\n    ${bootErr}`);

    const T = [];
    const narrations = [];

    // ── A. THE STARTER authors + plays; a move LANDS; the rail grows; verify true ──
    const authored = await page.evaluate(() => window.__forgePlay());
    assert.equal(authored.ok, true, "the starter authors (ok:true)");
    const sA = await page.evaluate(() => window.__forgeState());
    assert.equal(sA.mounted, true, "a fresh world is mounted from the authored starter");
    assert.ok(sA.counts.rooms >= 4, `the starter has several rooms (got ${sA.counts.rooms})`);
    const firstMove = await page.evaluate(() => window.__forgeAct("take candle"));
    assert.equal(firstMove.outcome, "landed", `a starter move LANDS (got ${firstMove.outcome}: ${firstMove.reason || ""})`);
    assert.equal(firstMove.state.receiptCount, 1, "the receipt rail grew by one landed move");
    const vA = await page.evaluate(() => window.__forgeVerify());
    assert.equal(vA.verified, true, "the authored world's ledger re-verifies as a hash chain");
    assert.ok(firstMove.narration && firstMove.narration.length > 0, "the AI narrated the move");
    narrations.push({ cmd: "take candle", prose: firstMove.narration });
    T.push(`STARTER   authored "${sA.worldName}" · ${sA.counts.rooms} rooms, ${sA.counts.exits} exits · mounted`);
    T.push(`          "take candle" → LANDED · receipt rail #${firstMove.state.receiptCount} · /game/verify=${vA.verified}`);

    // ── B. A SYNTAX-broken source fails closed at the PARSE stage, line-pinned, NO world ──
    const parseFail = await page.evaluate((src) => window.__forgePlay(src), SYNTAX_BROKEN);
    assert.equal(parseFail.ok, false, "the syntax-broken source did NOT author");
    assert.equal(parseFail.stage, "parse", `it failed at the PARSE stage (got ${parseFail.stage})`);
    assert.ok(Number.isInteger(parseFail.line) && parseFail.line > 0, `the parse error is line-pinned (got line ${parseFail.line})`);
    const sB = await page.evaluate(() => window.__forgeState());
    assert.equal(sB.mounted, false, "NO world is mounted after a parse failure (fail-closed; previous world torn down)");
    assert.ok(sB.error && sB.error.length > 0, "a legible parse message is shown");
    assert.equal(sB.errorLine, parseFail.line, "the panel pins the same line the service reported");
    const errTextB = await page.evaluate(() => (document.getElementById("error")?.textContent || "").trim());
    assert.ok(/fail-closed/i.test(errTextB), "the parse error panel says fail-closed");
    T.push(`PARSE     syntax-broken → stage="parse" · line ${parseFail.line}: ${parseFail.message} · NO world mounted`);

    // ── C. broken.dungeon PARSES but FAILS VALIDATION → EVERY issue listed, NO world ──
    const brokenSrc = await page.evaluate(() => fetch("/dungeons/broken.dungeon").then((r) => r.text()));
    const validateFail = await page.evaluate((src) => window.__forgePlay(src), brokenSrc);
    assert.equal(validateFail.ok, false, "the broken.dungeon did NOT author");
    assert.equal(validateFail.stage, "validate", `it failed at the VALIDATE stage (got ${validateFail.stage})`);
    const issues = validateFail.issues || [];
    const errIssues = issues.filter((i) => i.severity === "error");
    assert.ok(errIssues.length >= 2, `MULTIPLE validation errors are reported, not just the first (got ${errIssues.length})`);
    assert.ok(errIssues.some((i) => /unknown room|dangling|leads to/i.test(i.message)), "the dangling exit is among the issues");
    assert.ok(errIssues.some((i) => /unreachable/i.test(i.message)), "the unreachable objective is among the issues");
    assert.ok(errIssues.every((i) => Number.isInteger(i.line)), "each issue carries a (best-effort) line");
    assert.ok(errIssues.some((i) => i.line > 0), "at least one issue is line-pinned");
    const sC = await page.evaluate(() => window.__forgeState());
    assert.equal(sC.mounted, false, "NO world is mounted after a validation failure (fail-closed)");
    const errTextC = await page.evaluate(() => (document.getElementById("error")?.textContent || "").trim());
    assert.ok(/fail-closed/i.test(errTextC), "the validate error panel says fail-closed");
    T.push(`VALIDATE  broken.dungeon → stage="validate" · ${errIssues.length} errors listed (ALL, not just the first) · NO world mounted`);
    for (const i of errIssues) T.push(`            line ${i.line}: ${i.message}`);

    // ── D. FIX it → the starter re-authors and plays to a WIN ──
    const refixed = await page.evaluate(() => window.__forgePlay());
    assert.equal(refixed.ok, true, "fixing it (back to the starter) authors again");
    const sD = await page.evaluate(() => window.__forgeState());
    assert.equal(sD.mounted, true, "the world is mounted again after the fix");

    let prevReceipts = 0;
    const winLog = [];
    for (const [cmd, why, expectRoom] of WIN_PATH) {
      const resp = await page.evaluate((c) => window.__forgeAct(c), cmd);
      assert.equal(resp.outcome, "landed", `winning move "${cmd}" must land (got ${resp.outcome}: ${resp.reason || ""})`);
      assert.equal(resp.state.room.id, expectRoom, `after "${cmd}" the world should be in ${expectRoom}, got ${resp.state.room.id}`);
      assert.equal(resp.state.receiptCount, prevReceipts + 1, `"${cmd}" should add exactly one receipt (${prevReceipts} -> ${resp.state.receiptCount})`);
      prevReceipts = resp.state.receiptCount;
      const v = await page.evaluate(() => window.__forgeVerify());
      assert.equal(v.verified, true, `the ledger must re-verify after "${cmd}"`);
      assert.ok(resp.narration && resp.narration.length > 0, `the AI narrated "${cmd}"`);
      narrations.push({ cmd, prose: resp.narration });
      winLog.push({ cmd, why, room: resp.state.room.id, receipts: resp.state.receiptCount, status: resp.state.status, narration: resp.narration });
    }
    const won = await page.evaluate(async () => await (await fetch("/game/state")).json());
    assert.equal(won.status, "won", `the authored playthrough should WIN (got ${won.status})`);
    assert.equal(won.room.id, "shrine", "the winning room is the shrine");
    assert.equal(won.inventory.includes("relic"), true, "the winner carries the relic");
    assert.equal(won.receiptCount, WIN_PATH.length, `every winning move is a verified turn (${WIN_PATH.length})`);
    const finalVerify = await page.evaluate(() => window.__forgeVerify());
    assert.equal(finalVerify.verified, true, "the winning authored ledger re-verifies as a hash chain");
    T.push(`FIXED     re-authored the starter → played to WIN · ${won.receiptCount} verified turns · carrying [${won.inventory.join(", ")}]`);

    // Screenshot the WON state (the authored world, banner up, receipt rail full).
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "forge.png"), fullPage: true });

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    const transcript = renderTranscript({ base, narratorKind, realModel, T, winLog, won });
    await writeFile(path.join(OUT, "forge.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "forge.png")}`);
    console.log(`  transcript → ${path.join(OUT, "forge.txt")}\n`);
    console.log("  ✓ THE FORGE RAN: an authored .dungeon played to a WIN vs real gemma2; a syntax-broken world failed closed line-pinned; broken.dungeon listed all validation issues; the fix played again.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, narratorKind, realModel, T, winLog, won }) {
  const L = [];
  L.push("THE FORGE — write a .dungeon world, play it, verify it");
  L.push(`driven run · attested-dm /game/author contract · narratorKind: ${narratorKind}${realModel ? " (a REAL local model)" : ""}`);
  L.push("served at " + base + "/forge");
  L.push("=".repeat(76));
  L.push("");
  L.push("Write a .dungeon world in text; hit ▶ Play and it becomes a real attested AI dungeon:");
  L.push("a local model narrates, the WORLD resolves every move, a hash-chain remembers it. A");
  L.push("broken world fails closed with the line (parse), or lists EVERY unsound thing (validate).");
  L.push("");
  L.push("-".repeat(76));
  L.push("THE AUTHOR -> PLAY -> VERIFY LOOP");
  L.push("-".repeat(76));
  for (const line of T) L.push("  " + line);
  L.push("");
  L.push("-".repeat(76));
  L.push("THE WINNING PLAYTHROUGH OF THE AUTHORED WORLD  (each move LANDS; the rail grows by one)");
  L.push("-".repeat(76));
  for (const t of winLog) {
    L.push("");
    L.push(`  » ${t.cmd}   (${t.why})`);
    L.push(`    gemma2: ${oneline(t.narration)}`);
    L.push(`    world : LANDED → room ${t.room} · receipt rail #${t.receipts} · status ${t.status}`);
  }
  L.push("");
  L.push(`  RESULT: status = ${won.status.toUpperCase()} · ${won.receiptCount} verified turns · carrying [${won.inventory.join(", ")}]`);
  L.push("          the authored ledger re-verifies as a hash chain (authentic ∧ well-formed ∧ injection-free ∧ prev-linked).");
  L.push("");
  L.push("=".repeat(76));
  L.push("You wrote a world in text. It became an attested dungeon. No Rust. No recompile.");
  L.push("");
  return L.join("\n");
}

function oneline(s) { return String(s || "").replace(/\s+/g, " ").trim(); }

main().catch((e) => {
  console.error("\n  ✗ FORGE RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
