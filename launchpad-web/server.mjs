// server.mjs — the minimal backend for the dregg launchpad product layer.
//
//   node server.mjs
//     LAUNCHPAD_RPC=http://127.0.0.1:8545  (anvil / Base-Sepolia / Robinhood Chain)
//     LAUNCHPAD_ADDRESS=0x…                (the deployed DreggLaunchpad)
//
// Serves:
//   • the static product frontend (public/) — discovery, create, sale/bid, token
//   • the ethers UMD build at /vendor/ethers.js so the browser drives the REAL
//     contract with the SAME wallet the user already has (window.ethereum), the
//     drex-web "reuse the real wallet, no mock" pattern.
//   • GET  /api/config             → { rpc, address, abi } the browser wires up
//   • GET  /api/launches           → all launches, replayable-ranked (discovery)
//   • GET  /api/launches/:id        → one launch: disclosure + clearing + bids + holders
//   • POST /api/launches/:id/disclose → creator submits the raw disclosed schedule
//                                       + metadata; the server VERIFIES it against
//                                       the on-chain commitment (checkSchedule) and
//                                       stores it (the no-hidden-supply proof).
//
// The REST shape follows fiv3fingers/Token-Launchpad-Backend (routes/coin.ts:
// GET /coin list, GET /coin/:id detail, POST /coin/king trending) — reshaped to
// the fair-launch engine and a REPLAYABLE (not paid) ranking.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { LaunchpadIndexer } from './indexer.mjs';
import { NodeLaunchIndexer } from './node-indexer.mjs';
import { LAUNCHPAD_ABI, POOL_ABI } from './shared/abi.mjs';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const PUB = path.join(HERE, 'public');
const ETHERS_UMD = path.join(HERE, 'node_modules', 'ethers', 'dist', 'ethers.umd.min.js');

const PORT = process.env.PORT || 8785;
// Bind interface. UNSET (default) → Node binds all interfaces (the local-dev / gate
// behaviour, unchanged). On hbox the deploy unit sets LAUNCHPAD_HOST=100.95.240.73
// (the Tailscale iface, hbox-dregg) so ONLY tailnet peers — the AWS gateway — reach
// it; the public internet never can. NEVER 0.0.0.0 in the deployed unit. See
// deploy/launchpad/dregg-launchpad-web.service.
const HOST = process.env.LAUNCHPAD_HOST || undefined;
const RPC = process.env.LAUNCHPAD_RPC || 'http://127.0.0.1:8545';
const ADDRESS = process.env.LAUNCHPAD_ADDRESS || '';
// When DREGG_NODE is set the launchpad reads its launches from a LIVE dregg node
// (launches as a real turn stream — register/bid/clear turns executed on the
// effect-VM and proven by the node's prove_pool), instead of the EVM contract.
// This is the "node-driven, not a separate mock" source. HONEST: single-node dev
// instance; the EVM fair-launch contract remains the separate on-chain lane.
const DREGG_NODE = (process.env.DREGG_NODE || '').replace(/\/$/, '');

const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8',
  '.json': 'application/json', '.png': 'image/png', '.svg': 'image/svg+xml',
};

function send(res, code, body, type) {
  res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache',
    'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Content-Type',
    'Access-Control-Allow-Methods': 'GET,POST,OPTIONS' });
  res.end(body);
}
const json = (res, code, obj) => send(res, code, JSON.stringify(obj), MIME['.json']);

let indexer = null;

function readBody(req) {
  return new Promise((resolve) => {
    let b = '';
    req.on('data', (c) => { b += c; if (b.length > 1 << 20) req.destroy(); });
    req.on('end', () => resolve(b));
  });
}

async function handle(req, res) {
  const url = decodeURIComponent(req.url.split('?')[0]);
  if (req.method === 'OPTIONS') return send(res, 204, '');

  // ── API ──
  if (url === '/api/config') {
    return json(res, 200, {
      rpc: RPC, address: ADDRESS, abi: LAUNCHPAD_ABI, poolAbi: POOL_ABI,
      source: DREGG_NODE ? 'dregg-node' : 'evm', node: DREGG_NODE || null,
    });
  }
  if (url === '/api/launches' && req.method === 'GET') {
    if (!indexer) return json(res, 503, { error: 'indexer not ready' });
    return json(res, 200, { launches: indexer.list() });
  }
  const mDetail = url.match(/^\/api\/launches\/(\d+)$/);
  if (mDetail && req.method === 'GET') {
    const d = indexer && indexer.detail(mDetail[1]);
    return d ? json(res, 200, d) : json(res, 404, { error: 'no such launch' });
  }
  const mDisc = url.match(/^\/api\/launches\/(\d+)\/disclose$/);
  if (mDisc && req.method === 'POST') {
    if (!indexer) return json(res, 503, { error: 'indexer not ready' });
    try {
      const { schedule, meta } = JSON.parse(await readBody(req));
      const r = await indexer.submitDisclosure(mDisc[1], schedule, meta);
      return json(res, r.verified ? 200 : 409, r);
    } catch (e) { return json(res, 400, { error: String(e.message || e) }); }
  }

  // ── vendored ethers (browser drives the real contract with the real wallet) ──
  if (url === '/vendor/ethers.js') {
    return fs.readFile(ETHERS_UMD, (e, buf) => e ? send(res, 404, 'ethers not installed — run npm install')
      : send(res, 200, buf, MIME['.js']));
  }

  // ── static frontend ──
  let file = url === '/' ? path.join(PUB, 'index.html') : path.join(PUB, url);
  if (!path.resolve(file).startsWith(PUB)) return send(res, 403, 'forbidden');
  fs.readFile(file, (err, buf) => err ? send(res, 404, 'not found: ' + url)
    : send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream'));
}

async function main() {
  if (DREGG_NODE) {
    // NODE-DRIVEN: launches are a real turn stream on a live dregg node.
    indexer = await new NodeLaunchIndexer({ nodeUrl: DREGG_NODE }).start();
    console.log(`indexer: reading launches as real turns from dregg node ${DREGG_NODE}`);
    if (!indexer.up) console.log('  (node not reachable yet — the API will fill in as the node comes up)');
  } else if (ADDRESS) {
    indexer = await new LaunchpadIndexer({ rpcUrl: RPC, launchpad: ADDRESS }).start();
    console.log(`indexer: watching DreggLaunchpad ${ADDRESS} @ ${RPC}`);
  } else {
    console.log('WARNING: neither DREGG_NODE nor LAUNCHPAD_ADDRESS set — API will 503.');
    console.log('  node-driven:  DREGG_NODE=http://127.0.0.1:8420 node server.mjs');
  }
  http.createServer((req, res) => handle(req, res).catch((e) => json(res, 500, { error: String(e) })))
    .listen(PORT, HOST, () => {
      console.log(`dregg launchpad → http://${HOST || 'localhost'}:${PORT}`);
      console.log(`  discovery /  · create /create.html · token /token.html?id=1`);
    });
}
main();
