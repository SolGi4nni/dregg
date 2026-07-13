// serve.mjs — dev server for the DrEX web prototype.
//
//   node drex-web/serve.mjs   → http://localhost:8781
//
// Serves drex-web/ statically AND mounts the extension's wallet wasm at /wasm/
// so the page loads the SAME dregg_wasm.js + dregg_wasm_bg.wasm the browser
// extension ships — real in-browser proving, no copy, no mock.
//
// It ALSO exposes POST /clear — the REAL matcher + settlement. The web app posts
// the batch's revealed orders as JSON; the server shells to the `drex_clear`
// binary (intent/src/bin/drex_clear.rs), which runs the SAME pipeline as
// `cargo run -p dregg-intent --example drex_clear_book`: rung-2 aggregate →
// solver.rs multilateral ring match → verified_settle.rs (each leg folded through
// the proved recKExecAsset kernel) → allocations + conservation + reject-polarity.
// The clearing the UI renders is the REAL solver's, not a JS mirror.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const EXT = path.resolve(HERE, '..', 'extension');
const REPO = path.resolve(HERE, '..');
const PORT = process.env.PORT || 8781;

// How to invoke the REAL `drex_clear` matcher (intent/src/bin/drex_clear.rs).
//
// The Mac dev box is too contended to build Rust locally, so by default the
// matcher runs on the persvati build host where the binary is already compiled:
// we ssh in and pipe the orders JSON to the prebuilt binary over stdin. If a
// LOCAL binary exists (someone built it), we prefer it — same binary, no network.
// Override the host/dir with DREX_REMOTE / DREX_REMOTE_DIR.
const REMOTE_HOST = process.env.DREX_REMOTE || 'persvati';
const REMOTE_DIR = process.env.DREX_REMOTE_DIR || 'dregg-build/drex-matcher';

function drexClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'drex_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  return {
    cmd: 'ssh',
    args: [REMOTE_HOST, `cd ${REMOTE_DIR} && ./target/debug/drex_clear`],
    where: REMOTE_HOST + ':' + REMOTE_DIR + ' (prebuilt)',
  };
}

// Run the REAL clear-book pipeline over the posted revealed orders.
function runClear(ordersJson) {
  return new Promise((resolve) => {
    const { cmd, args } = drexClearCmd();
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', (e) => resolve({ ok: false, error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try {
        resolve(JSON.parse(line));
      } catch (_e) {
        resolve({ ok: false, error: 'drex_clear produced no JSON (exit ' + code + ')', stderr: err.slice(-400), raw: out.slice(-400) });
      }
    });
    child.stdin.end(ordersJson);
  });
}

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.wasm': 'application/wasm',
  '.json': 'application/json',
  '.png': 'image/png',
  '.svg': 'image/svg+xml',
};

function send(res, code, body, type) {
  res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache' });
  res.end(body);
}

http.createServer((req, res) => {
  let url = decodeURIComponent(req.url.split('?')[0]);
  if (url === '/') url = '/index.html';

  // ── POST /clear — the REAL matcher + verified settlement ──
  if (req.method === 'POST' && url === '/clear') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      const result = await runClear(body);
      send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
    });
    return;
  }

  let file;
  if (url.startsWith('/wasm/')) {
    file = path.join(EXT, url.slice('/wasm/'.length));
  } else {
    file = path.join(HERE, url);
  }
  // prevent path escape
  const root = url.startsWith('/wasm/') ? EXT : HERE;
  if (!path.resolve(file).startsWith(root)) return send(res, 403, 'forbidden');

  fs.readFile(file, (err, buf) => {
    if (err) return send(res, 404, 'not found: ' + url);
    send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream');
  });
}).listen(PORT, () => {
  console.log('DrEX dev server → http://localhost:' + PORT);
  console.log('  wallet wasm mounted from ' + EXT + '  (/wasm/dregg_wasm.js)');
  const { where } = drexClearCmd();
  console.log('  REAL matcher   POST /clear → drex_clear @ ' + where + '  (solver.rs + verified_settle.rs)');
});
