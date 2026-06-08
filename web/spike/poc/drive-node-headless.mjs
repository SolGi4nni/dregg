// drive-node-headless.mjs — boot the in-browser dregg NODE page (node.html) in
// REAL headless Chrome (no puppeteer/npm), let it connect to the live devnet,
// sync mesh state, locally-verify two turns with the wasm Lean executor, and
// attempt an API-relayed submit. Reports the REAL in-browser outcomes.
//
//   node web/spike/poc/drive-node-headless.mjs [endpoint]
//
// endpoint defaults to the live devnet. The page fetches it cross-origin; the
// node's /api/* responses carry permissive CORS, so this is a genuine
// cross-origin browser->node interaction, not a same-origin shim.
import { spawn } from "node:child_process";
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const SPIKE = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const PORT = 8012;
const CDP_PORT = 9223;
const CHROME = process.env.CHROME ||
  "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
const ENDPOINT = process.argv[2] || "https://devnet.dregg.fg-goose.online";

const MIME = { ".html":"text/html", ".js":"text/javascript", ".mjs":"text/javascript",
  ".wasm":"application/wasm", ".json":"application/json", ".css":"text/css" };

// Static server for web/spike. NOTE: deliberately NO COOP/COEP headers here —
// cross-origin-embedder-policy:require-corp would block the page's
// cross-origin fetches to the devnet API. The wasm is single-threaded so we
// don't need cross-origin isolation.
const server = http.createServer((req, res) => {
  let p = decodeURIComponent(req.url.split("?")[0]);
  if (p === "/") p = "/poc/node.html";
  const fp = path.join(SPIKE, p);
  if (!fp.startsWith(SPIKE) || !fs.existsSync(fp) || fs.statSync(fp).isDirectory()) {
    res.writeHead(404); res.end("404"); return;
  }
  res.setHeader("Content-Type", MIME[path.extname(fp)] || "application/octet-stream");
  fs.createReadStream(fp).pipe(res);
});

async function cdp() {
  const list = await fetch(`http://127.0.0.1:${CDP_PORT}/json`).then(r => r.json());
  const page = list.find(t => t.type === "page") || list[0];
  return page.webSocketDebuggerUrl;
}

async function main() {
  await new Promise(r => server.listen(PORT, r));
  const url = `http://127.0.0.1:${PORT}/poc/node.html?endpoint=${encodeURIComponent(ENDPOINT)}`;
  console.log(`[node] serving ${SPIKE} on :${PORT}`);
  console.log(`[node] endpoint = ${ENDPOINT}`);

  const userDir = fs.mkdtempSync("/tmp/node-chrome-");
  const chrome = spawn(CHROME, [
    "--headless=new", `--remote-debugging-port=${CDP_PORT}`,
    `--user-data-dir=${userDir}`, "--no-first-run", "--no-default-browser-check",
    "--disable-gpu", url,
  ], { stdio: ["ignore", "ignore", "pipe"] });

  let wsUrl;
  for (let i = 0; i < 100; i++) {
    try { wsUrl = await cdp(); break; } catch { await new Promise(r => setTimeout(r, 100)); }
  }
  if (!wsUrl) { console.error("[node] CDP never came up"); chrome.kill(); server.close(); process.exit(2); }

  const ws = new WebSocket(wsUrl);
  let id = 0; const pend = new Map();
  const send = (method, params={}) => new Promise(res => { const i = ++id; pend.set(i, res); ws.send(JSON.stringify({ id:i, method, params })); });
  await new Promise(r => ws.addEventListener("open", r, { once:true }));
  ws.addEventListener("message", ev => {
    const m = JSON.parse(ev.data);
    if (m.id && pend.has(m.id)) { pend.get(m.id)(m.result); pend.delete(m.id); }
  });
  await send("Runtime.enable");
  await send("Page.enable");

  // After local-verify completes the page can trigger a submit so we observe
  // the real relay outcome too. Wait for the wasm verdict first (CPU-bound
  // boot of a 42MB wasm can take a few seconds), then click submit.
  const evalJson = async (expr) => {
    const r = await send("Runtime.evaluate", { expression: expr, returnByValue: true });
    try { return JSON.parse(r?.result?.value ?? "null"); } catch { return null; }
  };

  let res = null;
  for (let i = 0; i < 400; i++) {       // up to ~40s (wasm boot + sync)
    res = await evalJson("JSON.stringify(window.__NODE_RESULT__ || null)");
    if (res && res.localVerify && res.localVerify.commit !== undefined && res.sync) break;
    await new Promise(r => setTimeout(r, 100));
  }

  // Fire the submit and capture its real outcome.
  await send("Runtime.evaluate", { expression: "document.getElementById('submit').click()" });
  let submit = null;
  for (let i = 0; i < 150; i++) {       // up to ~18s
    const r = await evalJson("JSON.stringify((window.__NODE_RESULT__||{}).submit||null)");
    if (r) { submit = r; break; }
    await new Promise(r => setTimeout(r, 120));
  }

  const dom = await evalJson(
    "JSON.stringify({title:document.title,conn:document.getElementById('conn').innerText,"+
    "vstatus:document.getElementById('vstatus').innerText,"+
    "sout:document.getElementById('sout').innerText})");

  console.log("\n[node] === in-browser (headless Chrome) result ===");
  console.log("[node] title          :", dom?.title);
  console.log("[node] connection     :", dom?.conn);
  console.log("[node] local-verify   :", dom?.vstatus);
  if (res?.localVerify) console.log("[node]   commit/rollback:", JSON.stringify(res.localVerify));
  if (res?.sync) console.log("[node] mesh sync      :", JSON.stringify(res.sync));
  console.log("[node] submit (relay) :", dom?.sout?.split("\n")[0]);
  if (submit) console.log("[node]   submit detail :", JSON.stringify(submit));
  const pass = !!(res && res.localVerify && res.localVerify.commit && res.localVerify.rollback);
  console.log("[node] verdict        :", pass ? "PASS (verified executor ran in-browser)" : "FAIL/TIMEOUT");

  ws.close(); chrome.kill(); server.close();
  process.exit(pass ? 0 : 1);
}

main().catch(e => { console.error(e); process.exit(3); });
