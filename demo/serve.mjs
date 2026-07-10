// The Commons demo — a tiny self-contained static server.
//
// Why a server (not a bare file:// open): the page loads an ES-bundled module and a
// wasm binary, and the wasm-bindgen glue instantiates the module via
// `instantiateStreaming`, which needs a real HTTP origin + `application/wasm` MIME.
// So we serve, rather than double-click.
//
// It bundles `app.ts` (the element + engine wiring) on startup with esbuild, and
// serves it alongside the page, the wasm glue + binary (from ../extension), and the
// scene. `run.mjs` reuses `buildApp` + `makeServer` to drive the same page headless.
//
//   node demo/serve.mjs        → serves at http://127.0.0.1:8787 (open it)
//   node demo/serve.mjs 9000   → serves on a chosen port

import http from "node:http";
import { readFile } from "node:fs/promises";
import { createReadStream } from "node:fs";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";
import { createDmStandin } from "./dm-standin.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const EXT = path.join(REPO, "extension");

// esbuild lives under extension/node_modules; resolve it from there.
const extRequire = createRequire(path.join(EXT, "package.json"));
const esbuild = extRequire("esbuild");

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
  ".scene": "text/plain; charset=utf-8",
  ".dungeon": "text/plain; charset=utf-8",
  ".txt": "text/plain; charset=utf-8",
};

/** Bundle a page-side TS entry to an inline-sourcemapped IIFE. */
async function bundle(entry) {
  const out = await esbuild.build({
    entryPoints: [path.join(__dirname, entry)],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2022"],
    sourcemap: "inline",
    write: false,
    logLevel: "silent",
  });
  return out.outputFiles[0].text;
}

/** Bundle the page-side app (imports the shipping element + engine from ../extension/src). */
export async function buildApp() {
  return bundle("app.ts");
}

/** Bundle THE AUTHORING SURFACE (write a .scene, compile + play it live, in-tab). */
export async function buildAuthor() {
  return bundle("author.ts");
}

/** Bundle the dungeon play surface (self-contained — only speaks the DM service over fetch). */
export async function buildDungeon() {
  return bundle("dungeon.ts");
}

/** Bundle THE SUNKEN VAULT play surface (self-contained — only speaks the /game service). */
export async function buildVault() {
  return bundle("vault.ts");
}

/** Bundle THE COLLECTIVE DUNGEON play surface (self-contained — only speaks the /party + /game service). */
export async function buildParty() {
  return bundle("party.ts");
}

/** Bundle THE FORGE (write a .dungeon, author + play it live over the /game service). */
export async function buildForge() {
  return bundle("forge.ts");
}

// ── The DM service ────────────────────────────────────────────────────────────
// By default the dungeon page is served against an in-memory STAND-IN (narratorKind
// "scripted") so `node demo/serve.mjs` is instantly playable. Set `DM_URL` (the parallel
// native lane's `attested-dm` HTTP service, documented on port 8790) to PROXY /narrate,
// /world, /verify to the REAL service instead (narratorKind "model:gemma2:2b").
const DM_URL = process.env.DM_URL || (process.env.DM_PORT ? `http://127.0.0.1:${process.env.DM_PORT}` : null);

async function readBody(req) {
  const chunks = [];
  for await (const c of req) chunks.push(c);
  return Buffer.concat(chunks).toString("utf8");
}

/** Handle a DM endpoint against the in-memory stand-in, or proxy to the real service. */
async function handleDm(url, method, body, dm, res) {
  if (DM_URL) {
    const r = await fetch(`${DM_URL}${url}`, {
      method,
      headers: { "content-type": "application/json", accept: "application/json" },
      body: method === "POST" ? body : undefined,
    });
    const text = await r.text();
    res.writeHead(r.status, { "content-type": "application/json; charset=utf-8" });
    return res.end(text);
  }
  let out;
  if (url === "/narrate" && method === "POST") {
    let msg = "";
    try { msg = (JSON.parse(body || "{}").player) ?? ""; } catch {}
    out = dm.narrate(String(msg));
  } else if (url === "/world" && method === "GET") {
    out = dm.world();
  } else if (url === "/verify" && method === "GET") {
    out = dm.verify();
  } else {
    res.writeHead(405, { "content-type": "text/plain" });
    return res.end("method not allowed");
  }
  res.writeHead(200, { "content-type": "application/json; charset=utf-8" });
  res.end(JSON.stringify(out));
}

/** Serve both demos. Returns { server, base, dm } (dm = the in-memory stand-in, or null when proxying). */
export async function makeServer(port = 0, opts = {}) {
  const appJs = await buildApp();
  const authorJs = await buildAuthor();
  const dungeonJs = await buildDungeon();
  const vaultJs = await buildVault();
  const partyJs = await buildParty();
  const forgeJs = await buildForge();
  const index = await readFile(path.join(__dirname, "index.html"), "utf8");
  const dungeon = await readFile(path.join(__dirname, "dungeon.html"), "utf8");
  const vault = await readFile(path.join(__dirname, "vault.html"), "utf8");
  const party = await readFile(path.join(__dirname, "party.html"), "utf8");
  const hub = await readFile(path.join(__dirname, "hub.html"), "utf8");
  const author = await readFile(path.join(__dirname, "author.html"), "utf8");
  const forge = await readFile(path.join(__dirname, "forge.html"), "utf8");
  const scene = await readFile(path.join(__dirname, "stories", "the-commons.scene"), "utf8");
  const STORIES_DIR = path.join(__dirname, "stories");
  // The committed .dungeon samples the Forge editor loads (read-only, from the attested-dm crate).
  const DUNGEONS_DIR = path.join(REPO, "attested-dm", "dungeons");

  // The DM world: an in-memory stand-in (default) unless proxying to the real service.
  const dm = DM_URL ? null : (opts.dm ?? createDmStandin(opts.dmOptions));

  const server = http.createServer(async (req, res) => {
    try {
      const url = (req.url || "/").split("?")[0];
      const method = (req.method || "GET").toUpperCase();

      // ── the DM service endpoints (stand-in or proxied) ──
      if (url === "/narrate" || url === "/world" || url === "/verify") {
        const body = method === "POST" ? await readBody(req) : null;
        return await handleDm(url, method, body, dm, res);
      }

      // ── THE SUNKEN VAULT /game endpoints AND THE COLLECTIVE DUNGEON /party endpoints —
      //    proxied to the native attested-dm service. There is no JS stand-in for either (both
      //    are a real GameSession over the engine); the page needs the native service
      //    (set DM_URL / DM_PORT). ──
      if (url.startsWith("/game/") || url.startsWith("/party/")) {
        if (!DM_URL) {
          res.writeHead(503, { "content-type": "application/json; charset=utf-8" });
          return res.end(JSON.stringify({ error: "the /game + /party API needs the native attested-dm dungeon-service; start it and set DM_URL or DM_PORT (default 8790)" }));
        }
        const body = method === "POST" ? await readBody(req) : undefined;
        const r = await fetch(`${DM_URL}${url}`, {
          method,
          headers: { "content-type": "application/json", accept: "application/json" },
          body,
        });
        const text = await r.text();
        res.writeHead(r.status, { "content-type": "application/json; charset=utf-8" });
        return res.end(text);
      }

      // ── The Commons (existing, unchanged) ──
      if (url === "/" || url === "/index.html") return send(res, index, MIME[".html"]);
      if (url === "/app.js") return send(res, appJs, MIME[".js"]);
      // Any `.scene` under stories/ (path-safe: basename only, must stay in the dir).
      if (url.startsWith("/stories/") && url.endsWith(".scene")) {
        const name = path.basename(url);
        const file = path.join(STORIES_DIR, name);
        if (path.dirname(file) !== STORIES_DIR) { res.writeHead(403); return res.end("forbidden"); }
        try {
          const body = await readFile(file, "utf8");
          return send(res, body, MIME[".scene"]);
        } catch {
          res.writeHead(404, { "content-type": "text/plain" });
          return res.end("scene not found");
        }
      }

      // ── The Authoring Surface (write a .scene, compile + play it live) ──
      if (url === "/author" || url === "/author.html") return send(res, author, MIME[".html"]);
      if (url === "/author.js") return send(res, authorJs, MIME[".js"]);
      if (url === "/dregg_wasm.js") {
        const js = await readFile(path.join(EXT, "dregg_wasm.js"), "utf8");
        return send(res, js, MIME[".js"]);
      }
      if (url === "/dregg_wasm_bg.wasm") {
        res.writeHead(200, { "content-type": MIME[".wasm"] });
        return createReadStream(path.join(EXT, "dregg_wasm_bg.wasm")).pipe(res);
      }

      // ── The Attested Dungeon (the play surface) ──
      if (url === "/dungeon" || url === "/dungeon.html") return send(res, dungeon, MIME[".html"]);
      if (url === "/dungeon.js") return send(res, dungeonJs, MIME[".js"]);

      // ── The Sunken Vault (the playable dungeon-crawler) ──
      if (url === "/vault" || url === "/vault.html") return send(res, vault, MIME[".html"]);
      if (url === "/hub" || url === "/games") return send(res, hub, MIME[".html"]);
      if (url === "/vault.js") return send(res, vaultJs, MIME[".js"]);

      // ── The Collective Dungeon (the crowd steers one party by vote) ──
      if (url === "/party" || url === "/party.html") return send(res, party, MIME[".html"]);
      if (url === "/party.js") return send(res, partyJs, MIME[".js"]);

      // ── The Forge (write a .dungeon, author + play it live over the /game service) ──
      if (url === "/forge" || url === "/forge.html") return send(res, forge, MIME[".html"]);
      if (url === "/forge.js") return send(res, forgeJs, MIME[".js"]);
      // The committed .dungeon samples (path-safe: basename only, must stay in the dir).
      if (url.startsWith("/dungeons/") && url.endsWith(".dungeon")) {
        const name = path.basename(url);
        const file = path.join(DUNGEONS_DIR, name);
        if (path.dirname(file) !== DUNGEONS_DIR) { res.writeHead(403); return res.end("forbidden"); }
        try {
          const body = await readFile(file, "utf8");
          return send(res, body, MIME[".dungeon"]);
        } catch {
          res.writeHead(404, { "content-type": "text/plain" });
          return res.end("dungeon not found");
        }
      }

      res.writeHead(404, { "content-type": "text/plain" });
      res.end("not found");
    } catch (e) {
      res.writeHead(500, { "content-type": "text/plain" });
      res.end(String(e?.message ?? e));
    }
  });
  await new Promise((r) => server.listen(port, "127.0.0.1", r));
  const { port: p } = server.address();
  return { server, base: `http://127.0.0.1:${p}`, dm };
}

function send(res, body, type) {
  res.writeHead(200, { "content-type": type });
  res.end(body);
}

// Run standalone: `node demo/serve.mjs [port]`
if (import.meta.url === `file://${process.argv[1]}`) {
  const port = Number(process.argv[2] || 8787);
  const { base } = await makeServer(port);
  console.log(`\n  The Commons — verifiable story demo`);
  console.log(`  open:  ${base}/`);
  console.log(`\n  Author — write a .scene, compile + play it live, in-tab (the authoring surface)`);
  console.log(`  open:  ${base}/author`);
  console.log(`\n  The Attested Dungeon — the model proposes, the capabilities dispose`);
  console.log(`  open:  ${base}/dungeon`);
  console.log(`  DM service: ${DM_URL ? "proxied → " + DM_URL : "in-memory stand-in (narratorKind scripted)"}`);
  console.log(`  (set DM_URL or DM_PORT to proxy to the native attested-dm service, e.g. DM_PORT=8790)\n`);
  console.log(`  THE SUNKEN VAULT — the AI narrates, the world resolves (playable dungeon-crawler)`);
  console.log(`  open:  ${base}/vault`);
  console.log(`  /game service: ${DM_URL ? "proxied → " + DM_URL : "NOT wired — set DM_URL or DM_PORT to the native attested-dm service (default 8790)"}\n`);
  console.log(`  THE COLLECTIVE DUNGEON — a crowd steers one party by vote (the crowd decides, the world resolves)`);
  console.log(`  open:  ${base}/party`);
  console.log(`  /party service: ${DM_URL ? "proxied → " + DM_URL : "NOT wired — set DM_URL or DM_PORT to the native attested-dm service (default 8790)"}\n`);
  console.log(`  THE FORGE — write a .dungeon world, hit ▶ Play, and it becomes a real attested AI dungeon (author → play → verify)`);
  console.log(`  open:  ${base}/forge`);
  console.log(`  /game service: ${DM_URL ? "proxied → " + DM_URL : "NOT wired — set DM_URL or DM_PORT to the native attested-dm service (default 8790)"}\n`);
  console.log(`  (Ctrl-C to stop)\n`);
}
