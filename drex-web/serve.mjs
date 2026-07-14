// serve.mjs — dev server for the DrEX web prototype.
//
//   node drex-web/serve.mjs   → http://localhost:8781
//
// Serves drex-web/ statically AND mounts the extension's wallet wasm at /wasm/
// so the page loads the SAME dregg_wasm.js + dregg_wasm_bg.wasm the browser
// extension ships — real in-browser proving, no copy, no mock.
//
// It ALSO exposes POST /clear — the REAL matcher. The web app posts the batch's
// revealed orders as JSON; the server shells to the `drex_clear` binary
// (intent/src/bin/drex_clear.rs), which runs the SAME pipeline as
// `cargo run -p dregg-intent --example drex_clear_book`: rung-2 aggregate →
// solver.rs multilateral ring match → verified_settle.rs (each leg folded through
// the proved recKExecAsset kernel) → allocations + conservation + reject-polarity.
// The clearing the UI renders is the REAL solver's, not a JS mirror.
//
// ── NODE-DRIVEN SETTLEMENT (the make-it-real unlock) ──
// POST /settle takes the cleared batch (the ring the solver found + allocations)
// and lands it as ONE real turn on a LIVE dregg node:
//   /cipherclerk/unlock  → bearer token (first unlock sets the dev passphrase)
//   POST /turn/submit     → the clearing settles as a real turn: SetField writes
//                           the per-trader allocations into the node ledger and
//                           EmitEvent records each ring leg. The node executes it
//                           on the effect-VM (execute_via_producer) and the async
//                           prove_pool proves it (a --prove-turns node additionally
//                           stores a full-turn STARK proof under /api/turn/{h}/proof).
//   GET  /api/turn/{h}/proof, /api/receipts, /api/cell/{op} → the proof, the
//                           committed receipt, and the ledger state — all read
//                           back FROM the node, not synthesized here.
// The node ingress is REAL; there is no faked node. If the node is unreachable,
// /settle returns { nodeUp:false } and the UI keeps the labeled local matcher.
// HONEST SCOPE: single-node dev instance (federation mode "solo"), not the
// multi-node BFT federation, and no on-chain settle (that is a separate wiring
// lane). The extension wallet + the solver + the node are all real.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const EXT = path.resolve(HERE, '..', 'extension');
const REPO = path.resolve(HERE, '..');
const PORT = process.env.PORT || 8781;

// The live dregg node the settlement lands on. Default: a local single-node dev
// instance (`dregg-node run --port 8420 --enable-faucet --prove-turns`), or the
// forwarded port of one run on a build host (`ssh -L 8420:localhost:8420 …`).
const NODE = (process.env.DREGG_NODE || 'http://127.0.0.1:8420').replace(/\/$/, '');
const NODE_PASSPHRASE = process.env.DREGG_NODE_PASSPHRASE || 'drex-dev-node';
let nodeBearer = null; // cached across requests once the node is unlocked.

// Unlock the node (idempotent): the FIRST unlock on a fresh data dir sets the
// dev passphrase and returns the bearer token that authorizes /turn/submit;
// later unlocks verify it. Loopback-only on the node side, which the local
// serve.mjs (or an ssh -L forward) satisfies.
async function nodeUnlock() {
  if (nodeBearer) return nodeBearer;
  const r = await fetch(NODE + '/cipherclerk/unlock', {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ passphrase: NODE_PASSPHRASE }),
  });
  const j = await r.json();
  if (!j.success || !j.bearer_token) throw new Error('node unlock failed: ' + (j.error || r.status));
  nodeBearer = j.bearer_token;
  return nodeBearer;
}

async function nodeGet(pathname) {
  const r = await fetch(NODE + pathname, { headers: nodeBearer ? { Authorization: 'Bearer ' + nodeBearer } : {} });
  if (!r.ok) return { __status: r.status };
  return r.json();
}

// A committed turn costs computrons, drawn against the operator cell's balance
// (the turn `fee` sets the budget). On a dev node the faucet tops the operator
// up so the settlement turn has budget. Materializes the cell if absent.
async function nodeFaucet(cell, amount) {
  try {
    await fetch(NODE + '/api/faucet', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ recipient: cell, amount }),
    });
  } catch (_e) { /* faucet may be disabled; the submit will report the real error */ }
}

// Encode a small unsigned int as a decimal string the node's parse_field_element
// packs little-endian into a field element (see node/src/api.rs).
const felt = (n) => String(Math.max(0, Math.min(Number.MAX_SAFE_INTEGER, Math.floor(Number(n) || 0))));

// Build the ONE settlement turn from the cleared batch and land it on the node.
async function settleOnNode(cleared) {
  const bearer = await nodeUnlock();
  const ident = await nodeGet('/api/node/identity');
  const operator = ident && ident.agent_cell;
  if (!operator) throw new Error('node identity has no agent cell');

  const allocs = (cleared.allocations || []).filter((a) => !a.rested);
  const legs = (cleared.ring && cleared.ring.legs) || [];
  const conserved = (cleared.conservation || []).reduce((s, c) => s + (Number(c.in) || 0), 0);

  // Effects on the operator's own cell (the node signs as itself and owns it):
  //   SetField index 0     = number of settled ring legs (a real state write)
  //   SetField index 1     = total conserved value across the batch (batch digest)
  //   SetField index 2+i   = trader i's received amount (the cleared allocation)
  //   EmitEvent drex_clear_leg per leg  → queryable via /api/events + receipts
  const effects = [
    { kind: 'set_field', index: 0, value: felt(legs.length) },
    { kind: 'set_field', index: 1, value: felt(conserved) },
  ];
  allocs.slice(0, 8).forEach((a, i) => {
    effects.push({ kind: 'set_field', index: 2 + i, value: felt(a.received) });
  });
  for (const l of legs) {
    effects.push({ kind: 'emit_event', topic: 'drex_clear_leg', data: [felt(l.amount)] });
  }
  effects.push({ kind: 'emit_event', topic: 'drex_clear_batch', data: [felt(legs.length), felt(conserved)] });

  // Budget: the turn fee sets the computron limit (must exceed the ~200/effect
  // the effect-VM charges) and the operator cell balance must back it. Top the
  // operator up first (faucet is 1/cell/min on a dev node, so keep the fee modest).
  const fee = 800 + 350 * effects.length;
  if ((ident.agent_balance || 0) < fee) {
    await nodeFaucet(operator, 10000);
    const re = await nodeGet('/api/node/identity');
    if (re && (re.agent_balance || 0) < fee) {
      throw new Error(`operator cell underfunded (have ${re.agent_balance}, need ${fee}); faucet is rate-limited — retry in ~1 min`);
    }
  }

  const submit = await fetch(NODE + '/turn/submit', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + bearer },
    body: JSON.stringify({ agent: operator, nonce: 0, fee, memo: 'drex_clear', actions: [{ effects }] }),
  }).then((r) => r.json());

  if (!submit.accepted || !submit.turn_hash) {
    return { nodeUp: true, accepted: false, operator, error: submit.error || 'turn not accepted', submit };
  }
  const turnHash = submit.turn_hash;

  // Poll for the async/committed proof + the committed receipt. The receipt comes
  // from /api/starbridge/receipts (it supports a turn_hash filter; the row nests
  // the ReceiptInfo under `.receipt`). The STARK proof (a --prove-turns node)
  // comes from /api/turn/{h}/proof; otherwise the async prove_pool attaches a
  // WitnessedReceipt (has_proof / witness_count on the receipt).
  // The receipt endpoint returns a flat ReceiptInfo (serde-flattened): turn_hash,
  // pre_state/post_state, computrons_used, action_count, has_proof, witness_count.
  let proof = null, r = null;
  for (let i = 0; i < 8; i++) {
    if (!proof) {
      const p = await nodeGet('/api/turn/' + turnHash + '/proof');
      if (p && !p.__status && p.proof_len) proof = { present: true, len: p.proof_len, mode: 'stark_full_turn' };
    }
    const recs = await nodeGet('/api/starbridge/receipts?turn_hash=' + turnHash);
    if (Array.isArray(recs) && recs.length) r = recs[0].receipt || recs[0];
    if (proof || (r && r.witness_count > 0)) break;
    await new Promise((x) => setTimeout(x, 500));
  }
  if (!proof && r && (r.witness_count > 0 || r.has_proof)) {
    proof = { present: true, len: null, mode: 'witnessed_receipt', witnessCount: r.witness_count };
  }
  // Honest proof-status note. The node ENQUEUES a real async STARK prove job
  // (prove_pool) for every committed state transition; when it lands it is
  // fetchable at /api/turn/{h}/proof. If it has not landed (or the effect-vm
  // rotated-IR prover cannot yet realize this effect's custom-table shape at the
  // node's HEAD), the turn is committed-but-unattested — surfaced, not hidden.
  const proofNote = proof
    ? null
    : 'prove_pool enqueued the async STARK job; no proof attached yet (committed-but-unattested)';

  const cell = await nodeGet('/api/cell/' + operator);

  return {
    nodeUp: true, accepted: true, node: NODE, operator, turnHash,
    proofStatus: submit.proof_status, witnessCount: submit.witness_count,
    proof: proof || { present: false }, proofNote,
    receipt: r && {
      chainIndex: r.chain_index, finality: r.finality,
      preState: r.pre_state, postState: r.post_state,
      computronsUsed: r.computrons_used, actionCount: r.action_count,
      hasProof: r.has_proof, witnessCount: r.witness_count,
      executorSigned: r.executor_signed,
    },
    cell: cell && !cell.__status && cell.found ? {
      balance: cell.balance, nonce: cell.nonce,
      stateCommitment: cell.state_commitment,
      fields: (cell.fields || []).slice(0, 10),
    } : null,
  };
}

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

http.createServer(async (req, res) => {
  let url = decodeURIComponent(req.url.split('?')[0]);
  if (url === '/') url = '/index.html';

  // ── POST /clear — the REAL matcher (solver.rs + verified_settle.rs) ──
  if (req.method === 'POST' && url === '/clear') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      const result = await runClear(body);
      send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
    });
    return;
  }

  // ── GET /node/status — is a live dregg node reachable? ──
  if (req.method === 'GET' && url === '/node/status') {
    try {
      const r = await fetch(NODE + '/status');
      const j = await r.json();
      return send(res, 200, JSON.stringify({ up: true, node: NODE, status: j }), MIME['.json']);
    } catch (e) {
      return send(res, 200, JSON.stringify({ up: false, node: NODE, error: e.message }), MIME['.json']);
    }
  }

  // ── POST /settle — land the cleared batch as ONE real turn on the live node ──
  if (req.method === 'POST' && url === '/settle') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      let cleared;
      try { cleared = JSON.parse(body); } catch (_e) { return send(res, 400, JSON.stringify({ error: 'bad json' }), MIME['.json']); }
      try {
        const result = await settleOnNode(cleared);
        send(res, 200, JSON.stringify(result), MIME['.json']);
      } catch (e) {
        // Node unreachable / unlock failed → the UI falls back to the labeled
        // local matcher path. This is the honest blocker surface, not a fake.
        send(res, 200, JSON.stringify({ nodeUp: false, node: NODE, error: e.message }), MIME['.json']);
      }
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
  console.log('  REAL matcher   POST /clear  → drex_clear @ ' + where + '  (solver.rs + verified_settle.rs)');
  console.log('  LIVE node      POST /settle → ' + NODE + '  (/turn/submit → effect-VM → prove_pool)');
  console.log('                 GET  /node/status probes it; start one with:');
  console.log('                 dregg-node run --port 8420 --enable-faucet --prove-turns');
});
