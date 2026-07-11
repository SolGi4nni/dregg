// THE DRIVEN RUN — THE OVERWORLD: the bundled dungeons as ONE navigable region, and a travel
// gate that OPENS on a verified win.
//
// Spawns the native attested-dm dungeon-service, serves the region page against it (serve.mjs
// proxying /game/*), loads /region in headless Chromium, and ASSERTS the INVARIANTS against the
// service's own /game/region contract (never fabricated):
//
//   A. GET /game/region returns the region graph (5 locations wiring the 5 games) + progress,
//      well-formed: every edge's endpoints are known locations. Fresh: 0/5 cleared, the road
//      tidewater → starfall is LOCKED (gated on clearing tidewater), and the page rendered the
//      SVG with the starfall node SEALED.
//   B. WIN the tidewater vault the honest way over HTTP (reset world=sunken-vault, then the full
//      solve via /game/act — each move LANDS; /game/verify stays green).
//   C. GET /game/region again: `tidewater` is now COMPLETED (credited only on the verified Won
//      chain), 1/5 cleared, and the road to `starfall` is now OPEN (the gate lifted). The page
//      re-renders with the starfall node AVAILABLE and tidewater CLEARED.
//
// The narration is a hosted/scripted model, so prose VARIES — we assert the graph + completion +
// gate states (the INVARIANTS), never the model's exact words.
//
// Captures demo/run/region.png + region.txt.

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

// The honest winning path through the tidewater vault (sunken-vault).
const SUNKEN_SOLVE = [
  "go north", "take lantern", "go down", "go down", "take rusted_key", "go north",
  "use rusted_key on iron_door", "go east", "take sword", "go north", "attack warden",
  "go east", "take amulet", "go up",
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

  // ── 1. spawn the native attested-dm dungeon-service ──
  const SERVICE_PORT = 8792;
  // Force the deterministic scripted narrator: this driver asserts the REGION + completion-gate
  // invariants, not the prose, and a 14-move winning solve should not depend on a live model.
  const svc = spawn(SERVICE_BIN, [], {
    env: { ...process.env, DUNGEON_BIND: `127.0.0.1:${SERVICE_PORT}`, DREGG_NARRATOR: "scripted" },
    stdio: ["ignore", "pipe", "pipe"],
  });
  const svcLog = [];
  svc.stdout.on("data", (d) => svcLog.push(String(d)));
  svc.stderr.on("data", (d) => svcLog.push(String(d)));
  svc.on("exit", (code) => { if (code) svcLog.push(`\n[service exited ${code}]`); });

  let server, browser;
  const pageErrors = [];
  try {
    await waitPortOpen(SERVICE_PORT);
    await new Promise((r) => setTimeout(r, 500));

    // ── 2. serve the region page against the native service (proxy /game/*) ──
    process.env.DM_PORT = String(SERVICE_PORT);
    const { makeServer } = await import("./serve.mjs");
    ({ server } = await makeServer(0));
    const base = server.address ? `http://127.0.0.1:${server.address().port}` : null;

    // ── 3. load the region page ──
    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1120, height: 1500 }, deviceScaleFactor: 2 });
    page.on("pageerror", (e) => pageErrors.push(String(e)));
    page.on("console", (m) => { if (m.type() === "error") pageErrors.push(`console: ${m.text()}`); });

    await page.goto(`${base}/region`, { waitUntil: "load" });
    await page.waitForFunction(() => window.__REGION_READY === true || !!window.__REGION_ERROR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__REGION_ERROR || null);
    if (bootErr) throw new Error(`the region page failed to boot (could not reach /game/region):\n    ${bootErr}`);

    const api = {
      get: async (p) => await (await fetch(`${base}${p}`)).json(),
      post: async (p, body) => await (await fetch(`${base}${p}`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body) })).json(),
    };

    // ── A. THE REGION GRAPH — well-formed, fresh, the deep road LOCKED ──
    const before = await api.get("/game/region");
    assert.ok(Array.isArray(before.locations) && before.locations.length === 5, `the region wires 5 dungeons (got ${before.locations?.length})`);
    assert.equal(before.total, 5, "the region reports 5 locations total");
    const ids = before.locations.map((l) => l.id).sort();
    assert.deepEqual(ids, ["deepdark", "starfall", "thornmarch", "tidewater", "venomdeep"], `the 5 locations (got ${ids.join(", ")})`);
    // Well-formed: every edge endpoint is a known location.
    const locSet = new Set(before.locations.map((l) => l.id));
    for (const e of before.edges) {
      assert.ok(locSet.has(e.from) && locSet.has(e.to), `edge ${e.from}->${e.to} touches only known locations`);
    }
    assert.equal(before.clearedCount, 0, "a fresh region has 0 cleared");
    assert.equal(before.locations.find((l) => l.id === "tidewater").completed, false, "tidewater starts uncleared");
    const gateBefore = before.edges.find((e) => e.from === "tidewater" && e.to === "starfall");
    assert.ok(gateBefore, "there is a road tidewater -> starfall");
    assert.equal(gateBefore.locked, true, "the road to the starfall spire starts BARRED (gated on tidewater)");
    assert.equal(before.locations.find((l) => l.id === "starfall").available, false, "the starfall spire is not reachable yet");

    // The page rendered the SVG with the starfall node SEALED (locked/completed states are visible).
    const svgOk = await page.evaluate(() => !!document.querySelector(".regionmap-svg"));
    assert.ok(svgOk, "the region page rendered the inline SVG map");
    const starfallStateBefore = await page.evaluate(() => document.querySelector('a.rg-link[data-loc="starfall"]')?.dataset.state);
    assert.equal(starfallStateBefore, "sealed", `the starfall node renders SEALED before the vault is cleared (got ${starfallStateBefore})`);
    const lockedEdgeDrawn = await page.evaluate(() => document.querySelectorAll(".rm-edge.locked").length);
    assert.ok(lockedEdgeDrawn >= 1, `at least one barred road is drawn distinctly (got ${lockedEdgeDrawn})`);

    console.log(`  A ok: 5 locations, ${lockedEdgeDrawn} barred road(s) drawn, starfall sealed`);

    // ── B. WIN THE TIDEWATER VAULT the honest way over HTTP ──
    const reset = await api.post("/game/reset", { world: "sunken-vault" });
    assert.equal(reset.state.world, "sunken-vault", "reset to the tidewater vault");
    const winLog = [];
    for (const cmd of SUNKEN_SOLVE) {
      const resp = await api.post("/game/act", { command: cmd });
      assert.equal(resp.outcome, "landed", `vault move "${cmd}" must land (got ${resp.outcome}: ${resp.reason || ""})`);
      winLog.push({ cmd, room: resp.state.room.id, status: resp.state.status });
    }
    const finalState = await api.get("/game/state");
    assert.equal(finalState.status, "won", `the tidewater vault is won (got ${finalState.status})`);
    const verify = await api.get("/game/verify");
    assert.equal(verify.verified, true, "the winning ledger re-verifies as a hash chain");

    // ── C. THE GATE OPENS — the region credits tidewater and unlocks the spire road ──
    const after = await api.get("/game/region");
    const tidewaterAfter = after.locations.find((l) => l.id === "tidewater");
    assert.equal(tidewaterAfter.completed, true, "tidewater is now CLEARED (credited only on the verified Won chain)");
    assert.equal(after.clearedCount, 1, "1/5 cleared after the verified win");
    const gateAfter = after.edges.find((e) => e.from === "tidewater" && e.to === "starfall");
    assert.equal(gateAfter.locked, false, "the road to the starfall spire is now OPEN (the gate lifted on the verified win)");
    assert.equal(after.locations.find((l) => l.id === "starfall").available, true, "the starfall spire is now reachable");

    // The page re-renders with the new states.
    await page.evaluate(async () => { await window.__regionRefresh(); });
    await page.waitForTimeout(150);
    const tidewaterStateAfter = await page.evaluate(() => document.querySelector('a.rg-link[data-loc="tidewater"]')?.dataset.state);
    const starfallStateAfter = await page.evaluate(() => document.querySelector('a.rg-link[data-loc="starfall"]')?.dataset.state);
    assert.equal(tidewaterStateAfter, "cleared", `the tidewater node renders CLEARED after the win (got ${tidewaterStateAfter})`);
    assert.equal(starfallStateAfter, "available", `the starfall node renders AVAILABLE after the gate opens (got ${starfallStateAfter})`);

    await page.waitForTimeout(200);
    await page.screenshot({ path: path.join(OUT, "region.png"), fullPage: true });

    if (pageErrors.length) console.warn("page console/errors:\n  " + pageErrors.join("\n  "));

    // ── transcript ──
    const transcript = renderTranscript({ base, before, after, winLog });
    await writeFile(path.join(OUT, "region.txt"), transcript, "utf8");
    console.log(transcript);
    console.log(`\n  screenshot → ${path.join(OUT, "region.png")}`);
    console.log(`  transcript → ${path.join(OUT, "region.txt")}\n`);
    console.log("  ✓ THE OVERWORLD RAN: five dungeons in one region over HTTP — the road to the starfall spire was BARRED, a genuinely won + verified tidewater vault CLEARED its node, and the gate OPENED. Travel is verified-completion-gated.\n");
  } catch (err) {
    console.error("  page errors:\n    " + (pageErrors.join("\n    ") || "(none)"));
    console.error("  service log tail:\n    " + svcLog.join("").split("\n").slice(-12).join("\n    "));
    throw err;
  } finally {
    if (browser) await browser.close();
    if (server) server.close();
    svc.kill("SIGTERM");
  }
}

function renderTranscript({ base, before, after, winLog }) {
  const L = [];
  L.push("THE OVERWORLD — the bundled dungeons as one navigable region · travel is verified-completion-gated");
  L.push(`driven run · attested-dm /game/region contract · served at ${base}/region`);
  L.push("=".repeat(80));
  L.push("");
  L.push(`REGION: ${before.region.name} — ${before.region.blurb}`);
  L.push("");
  L.push("A · THE MAP, FRESH  (GET /game/region)");
  L.push("-".repeat(80));
  L.push(`  cleared: ${before.clearedCount}/${before.total}`);
  for (const l of before.locations) {
    const state = l.completed ? "cleared" : l.current ? "you-are-here" : l.available ? "open" : "sealed";
    L.push(`  • ${l.id.padEnd(11)} ${l.name.padEnd(22)} [${state}]  (${l.gameId})`);
  }
  L.push("  roads:");
  for (const e of before.edges) {
    const g = e.gate ? ` gate=${e.gate}` : "";
    L.push(`    ${e.from.padEnd(11)} -> ${e.to.padEnd(11)} ${e.locked ? "BARRED" : "open  "}${g}${e.gateReason ? "  (" + e.gateReason + ")" : ""}`);
  }
  L.push("");
  L.push("-".repeat(80));
  L.push("B · WIN THE TIDEWATER VAULT  (reset world=sunken-vault; the honest solve over /game/act)");
  L.push("-".repeat(80));
  for (const t of winLog) {
    L.push(`  » ${t.cmd.padEnd(28)} → room ${t.room} · ${t.status}`);
  }
  L.push("");
  L.push("-".repeat(80));
  L.push("C · THE GATE OPENS  (GET /game/region — credited only on the verified Won chain)");
  L.push("-".repeat(80));
  L.push(`  cleared: ${after.clearedCount}/${after.total}`);
  const g2 = after.edges.find((e) => e.from === "tidewater" && e.to === "starfall");
  L.push(`  tidewater : ${after.locations.find((l) => l.id === "tidewater").completed ? "CLEARED ✓" : "uncleared"}`);
  L.push(`  road tidewater -> starfall : ${g2.locked ? "still barred" : "OPEN — the gate lifted"}`);
  L.push(`  starfall spire : ${after.locations.find((l) => l.id === "starfall").available ? "now reachable" : "still sealed"}`);
  L.push("");
  L.push("=".repeat(80));
  L.push("Five dungeons, one world. Each independently verified; each cleared ONLY on a re-verified Won");
  L.push("chain. The map opens as you honestly clear it. The ledger is the truth.");
  L.push("");
  return L.join("\n");
}

main().catch((e) => {
  console.error("\n  ✗ OVERWORLD RUN FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});
