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

/** Bundle the dungeon play surface (self-contained — only speaks the DM service over fetch). */
export async function buildDungeon() {
  return bundle("dungeon.ts");
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
  const dungeonJs = await buildDungeon();
  const index = await readFile(path.join(__dirname, "index.html"), "utf8");
  const dungeon = await readFile(path.join(__dirname, "dungeon.html"), "utf8");
  const scene = await readFile(path.join(__dirname, "stories", "the-commons.scene"), "utf8");

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

      // ── The Commons (existing, unchanged) ──
      if (url === "/" || url === "/index.html") return send(res, index, MIME[".html"]);
      if (url === "/app.js") return send(res, appJs, MIME[".js"]);
      if (url === "/stories/the-commons.scene") return send(res, scene, MIME[".scene"]);
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
  console.log(`\n  The Attested Dungeon — the model proposes, the capabilities dispose`);
  console.log(`  open:  ${base}/dungeon`);
  console.log(`  DM service: ${DM_URL ? "proxied → " + DM_URL : "in-memory stand-in (narratorKind scripted)"}`);
  console.log(`  (set DM_URL or DM_PORT to proxy to the native attested-dm service, e.g. DM_PORT=8790)\n`);
  console.log(`  (Ctrl-C to stop)\n`);
}
