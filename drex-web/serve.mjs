// serve.mjs — dev server for the DrEX web prototype.
//
//   node drex-web/serve.mjs   → http://localhost:8781
//
// Serves drex-web/ statically AND mounts the extension's wallet wasm at /wasm/
// so the page loads the SAME dregg_wasm.js + dregg_wasm_bg.wasm the browser
// extension ships — real in-browser proving, no copy, no mock.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const EXT = path.resolve(HERE, '..', 'extension');
const PORT = process.env.PORT || 8781;

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
});
