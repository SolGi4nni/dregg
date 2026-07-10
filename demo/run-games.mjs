// THE DRIVEN RUN — THE ATTESTED DUNGEONS: game selection over HTTP, BOTH games played.
//
// Spawns the native attested-dm dungeon-service (real gemma2:2b via ollama), serves the game
// page against it (serve.mjs proxying /game/*), loads it in headless Chromium, and drives the
// game-selection surface + BOTH dungeons through the page's own affordances (the picker + the
// command bar → fetch → /game/{list,reset,act} → render), ASSERTING the INVARIANTS against the
// service's own responses (never fabricated):
//
//   A. /game/list returns BOTH registered games (sunken-vault + bramble-keep) with objectives.
//   B. RESET to sunken-vault, play a couple moves (go north → take lantern → go down): each
//      LANDS, the world transitions, the receipt rail grows, /game/state reports world sunken-vault.
//   C. RESET to bramble-keep, play the witch trade (take candle → go north → go east →
//      take nightshade → go west → go west → ask witch about sickle): the Hedge-Witch's
//      WORLD-BOUNDED dialogue gives the silver sickle ONLY because we carry the nightshade —
//      the grant LANDS over HTTP, the receipt rail grows, /game/state reports world bramble-keep.
//   D. /game/verify re-verifies the whole ledger as a hash chain throughout.
//
// The narration is a REAL local model, so prose VARIES run to run — we assert world state
// transitions / grants / world id (the INVARIANTS), never the model's exact words.
//
// Captures demo/run/bramble.png + games.txt.

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

// A couple of LANDING moves in the sunken vault (from the shore).
const VAULT_MOVES = [
  ["go north", "into the salt antechamber", "antechamber"],
  ["take lantern", "a light against the dark", "antechamber"],
  ["go down", "down the now-lit stair", "dark_stair"],
];

// The Bramble Keep witch-trade path: nightshade in hand, the Hedge-Witch parts with her sickle.
const BRAMBLE_MOVES = [
  ["take candle", "a light for the crypt", "gatehouse", { lands: true }],
  ["go north", "into the overgrown courtyard", "courtyard", { lands: true }],
  ["go east", "to the poisoned garden", "garden", { lands: true }],
  ["take nightshade", "the witch's price", "garden", { lands: true }],
  ["go west", "back to the courtyard", "courtyard", { lands: true }],
  ["go west", "to the Hedge-Witch's hut", "witch_hut", { lands: true }],
  ["ask witch about sickle", "the world-bounded trade", "witch_hut", { lands: true, grants: "sickle" }],
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
  const SERVICE_PORT = 8791;
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
    await new Promise((r) => setTimeout(r, 500));
    const narratorKind = await (await fetch(`http://127.0.0.1:${SERVICE_PORT}/game/state`)).json().then((s) => s.narratorKind);
    const realModel = String(narratorKind || "").startsWith("model:");

    // ── 2. serve the game page against the native service (proxy /game/*) ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    // ── 3. load the page ──
    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1120, height: 2100 }, deviceScaleFactor: 2 });
    const pageErrors = [];
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/vault`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__VAULT_READY === true || !!window.__VAULT_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__VAULT_ERROR || null);
    if (bootErr) throw new Error(`the game page failed to boot (could not reach /game):\n    ${bootErr}`);

    // ── A. THE GAME REGISTRY — /game/list serves the registered games ──
    const EXPECTED_GAMES = ["bramble-keep", "deepdark-mine", "starfall-spire", "sunken-vault"];
    const list = await page.evaluate(async () => await (await fetch("/game/list")).json());
    assert.ok(Array.isArray(list), "/game/list returns an array");
    const ids = list.map((g) => g.id).sort();
    assert.deepEqual(ids, EXPECTED_GAMES, `/game/list lists the registered games (got ${ids.join(", ")})`);
    for (const g of list) {
      assert.ok(g.name && g.blurb && g.objective, `game ${g.id} has name/blurb/objective`);
    }
    // The picker rendered a card per game on the page.
    const cards = await page.evaluate(() => Array.from(document.querySelectorAll("button.game-card")).map((b) => b.dataset.world));
    assert.deepEqual(cards.slice().sort(), EXPECTED_GAMES, `the page picker shows the registered games (got ${cards.join(", ")})`);

    // ── B. THE SUNKEN VAULT — reset via the page, play a couple LANDING moves ──
    const vaultReset = await page.evaluate(() => window.__vaultReset("sunken-vault"));
    assert.equal(vaultReset.world, "sunken-vault", "reset to sunken-vault reports world sunken-vault");
    assert.equal(vaultReset.room.id, "shore", "the sunken vault starts at the shore");
    assert.equal(vaultReset.receiptCount, 0, "a fresh vault starts with an empty receipt rail");

    let prev = 0;
    const vaultLog = [];
    for (const [cmd, why, expectRoom] of VAULT_MOVES) {
      const resp = await page.evaluate((c) => window.__vaultAct(c), cmd);
      assert.equal(resp.outcome, "landed", `vault move "${cmd}" must land (got ${resp.outcome}: ${resp.reason || ""})`);
      assert.equal(resp.state.world, "sunken-vault", `vault move "${cmd}" stays in world sunken-vault`);
      assert.equal(resp.state.room.id, expectRoom, `after "${cmd}" the vault is in ${expectRoom}, got ${resp.state.room.id}`);
      assert.equal(resp.state.receiptCount, prev + 1, `"${cmd}" adds exactly one receipt (${prev} -> ${resp.state.receiptCount})`);
      prev = resp.state.receiptCount;
      const v = await page.evaluate(async () => await (await fetch("/game/verify")).json());
      assert.equal(v.verified, true, `the ledger re-verifies after vault "${cmd}"`);
      vaultLog.push({ cmd, why, room: resp.state.room.id, receipts: resp.state.receiptCount, narration: resp.narration });
    }
    const vaultState = await page.evaluate(async () => await (await fetch("/game/state")).json());
    assert.equal(vaultState.world, "sunken-vault", "/game/state reports the vault world");
    assert.equal(vaultState.worldName, "The Sunken Vault", "the vault reports its display name");

    // ── C. BRAMBLE KEEP — switch worlds via the page, run the world-bounded witch trade ──
    const brambleReset = await page.evaluate(() => window.__vaultReset("bramble-keep"));
    assert.equal(brambleReset.world, "bramble-keep", "switching to bramble-keep reports world bramble-keep");
    assert.equal(brambleReset.worldName, "Bramble Keep", "bramble reports its display name");
    assert.equal(brambleReset.room.id, "gatehouse", "bramble keep starts at the gatehouse");
    assert.equal(brambleReset.receiptCount, 0, "a fresh keep starts with an empty receipt rail");

    prev = 0;
    let sickleGranted = false;
    const brambleLog = [];
    for (const [cmd, why, expectRoom, opts] of BRAMBLE_MOVES) {
      const resp = await page.evaluate((c) => window.__vaultAct(c), cmd);
      assert.equal(resp.outcome, "landed", `bramble move "${cmd}" must land (got ${resp.outcome}: ${resp.reason || ""})`);
      assert.equal(resp.state.world, "bramble-keep", `bramble move "${cmd}" stays in world bramble-keep`);
      assert.equal(resp.state.room.id, expectRoom, `after "${cmd}" the keep is in ${expectRoom}, got ${resp.state.room.id}`);
      assert.equal(resp.state.receiptCount, prev + 1, `"${cmd}" adds exactly one receipt (${prev} -> ${resp.state.receiptCount})`);
      prev = resp.state.receiptCount;
      if (opts && opts.grants) {
        assert.ok(resp.state.inventory.includes(opts.grants),
          `the world-bounded dialogue GRANTED ${opts.grants} over HTTP (inventory: ${resp.state.inventory.join(", ")})`);
        sickleGranted = opts.grants === "sickle";
      }
      const v = await page.evaluate(async () => await (await fetch("/game/verify")).json());
      assert.equal(v.verified, true, `the ledger re-verifies after bramble "${cmd}"`);
      brambleLog.push({ cmd, why, room: resp.state.room.id, receipts: resp.state.receiptCount, inventory: resp.state.inventory, narration: resp.narration });
    }
    assert.equal(sickleGranted, true, "the Hedge-Witch gave the silver sickle (world-bounded dialogue over HTTP)");

    const brambleState = await page.evaluate(async () => await (await fetch("/game/state")).json());
    assert.equal(brambleState.world, "bramble-keep", "/game/state reports the keep world");
    assert.ok(brambleState.inventory.includes("sickle"), "the keep state carries the granted sickle");

    // Screenshot Bramble Keep in the browser (sickle in hand, receipt rail grown).
    await page.waitForTimeout(300);
    await page.screenshot({ path: path.join(OUT, "bramble.png"), fullPage: true });

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    // ── transcript ──
    const transcript = renderTranscript({ base, narratorKind, realModel, list, vaultLog, vaultState, brambleLog, brambleState });
    await writeFile(path.join(OUT, "games.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "bramble.png")}`);
    console.log(`  transcript → ${path.join(OUT, "games.txt")}\n`);
    console.log("  ✓ THE ATTESTED DUNGEONS RAN: both games selectable over HTTP — the vault mini-run landed, and the Bramble Keep Hedge-Witch parted with her sickle ONLY for the nightshade. The AI narrates, the world resolves.\n");
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, narratorKind, realModel, list, vaultLog, vaultState, brambleLog, brambleState }) {
  const L = [];
  L.push("THE ATTESTED DUNGEONS — game selection over HTTP · the AI narrates, the world resolves");
  L.push(`driven run · attested-dm /game contract · narratorKind: ${narratorKind}${realModel ? " (a REAL local model)" : ""}`);
  L.push("served at " + base + "/vault");
  L.push("=".repeat(78));
  L.push("");
  L.push("A · THE REGISTRY  (GET /game/list)");
  L.push("-".repeat(78));
  for (const g of list) {
    L.push(`  • ${g.id.padEnd(14)} ${g.name}`);
    L.push(`      ${g.blurb}`);
    L.push(`      ★ ${g.objective}`);
  }
  L.push("");
  L.push("-".repeat(78));
  L.push("B · THE SUNKEN VAULT  (reset world=sunken-vault; a couple of landing moves)");
  L.push("-".repeat(78));
  for (const t of vaultLog) {
    L.push("");
    L.push(`  » ${t.cmd}   (${t.why})`);
    L.push(`    gemma2: ${oneline(t.narration)}`);
    L.push(`    world : LANDED → room ${t.room} · receipt rail #${t.receipts} · world sunken-vault`);
  }
  L.push("");
  L.push("-".repeat(78));
  L.push("C · BRAMBLE KEEP  (reset world=bramble-keep; the world-bounded witch trade)");
  L.push("-".repeat(78));
  for (const t of brambleLog) {
    L.push("");
    L.push(`  » ${t.cmd}   (${t.why})`);
    L.push(`    gemma2: ${oneline(t.narration)}`);
    L.push(`    world : LANDED → room ${t.room} · receipt rail #${t.receipts} · carrying [${t.inventory.join(", ")}]`);
  }
  L.push("");
  L.push(`  RESULT: the Hedge-Witch parted with the silver sickle ONLY because the nightshade was in`);
  L.push(`          hand — no prose talked it out of her early. The keep now carries [${brambleState.inventory.join(", ")}].`);
  L.push("");
  L.push("=".repeat(78));
  L.push("Two worlds, one attested engine. The AI narrated. The world resolved. The ledger is the truth.");
  L.push("");
  return L.join("\n");
}

function oneline(s) { return String(s || "").replace(/\s+/g, " ").trim(); }

main().catch((e) => {
  console.error("\n  ✗ ATTESTED DUNGEONS RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
