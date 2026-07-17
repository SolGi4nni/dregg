// serve.mjs — the DrEX v2 dev server. A SEPARATE file + port (8782) from the
// legacy demo's serve.mjs (:8781) and offerings.mjs (:8790), so it never
// clobbers the live drex-web lanes. It serves the v2 static app (index.html,
// styles.css, dist/) and exposes the SAME REAL endpoints the app calls — this is
// the FULL endpoint surface (the v1 :8781 routes are ported here, so v2 is the
// primary DrEX terminal, not a partial seed):
//
//   POST /clear           → the REAL matcher (drex_clear: solver.rs ring match →
//                           verified_settle.rs kernel fold). Local binary first,
//                           else ssh the prebuilt matcher on the build host.
//   POST /clear-shielded  → the REAL fhEgg single-phase shielded clearing
//                           (fhegg_clear: PDHG circulation + Cert-F certificate +
//                           the verified AIR gate). LOCAL only; honest
//                           "not built" error if the binary is absent.
//   POST /prove-shielded  → the REAL reveal-nothing STARK (cert_f_prove). The
//                           solver certificate (f/π/s) stays SERVER-SIDE; the
//                           browser gets only the world-visible scalars. Honest
//                           "not built" error if the binary is absent.
//   GET  /node/status     → probe a live dregg node (for the settle path).
//   POST /settle          → land the cleared batch as ONE real turn on the live
//                           node (per-trader Transfer + batch EmitEvent), read
//                           the proof + committed receipt + each trader's balance
//                           BACK from the node. If no node, { nodeUp:false } and
//                           the UI keeps the labelled local-clear result.
//
// `node serve.mjs --check` runs a no-listen self-check: static assets, engine
// binaries (present vs honest-fallback), node reachability. Exit 1 only when the
// app bundle is missing (i.e. `npm run build` is needed).
//
// The wallet is NOT mounted here — v2 routes all signing through the INSTALLED
// extension (window.dregg), not a standalone wasm. Binds 127.0.0.1 by default
// (same all-interfaces guard shape as the existing servers).

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import crypto from 'node:crypto';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, '..');
const PORT = process.env.PORT || 8782;
const HOST = process.env.DREX_BIND || '127.0.0.1';
const CHECK = process.argv.includes('--check');
const WILDCARD = HOST === '0.0.0.0' || HOST === '::' || HOST === '*';
if (WILDCARD && process.env.DREX_ALLOW_WILDCARD !== '1') {
  console.error(`refusing to bind ${HOST} (all-interfaces = public unless a host firewall gates :${PORT}).`);
  console.error(`  set DREX_BIND=127.0.0.1 (default) or the LAN IP; wildcard needs DREX_ALLOW_WILDCARD=1 behind a firewall.`);
  process.exit(1);
}

const NODE = (process.env.DREGG_NODE || 'http://127.0.0.1:8420').replace(/\/$/, '');
const NODE_PASSPHRASE = process.env.DREGG_NODE_PASSPHRASE || 'drex-dev-node';
const REMOTE_HOST = process.env.DREX_REMOTE || 'persvati';
const REMOTE_DIR = process.env.DREX_REMOTE_DIR || 'dregg-build/drex-matcher';
let nodeBearer = null;

// ── engine binaries: locate local-first; honest fallbacks otherwise ──
function drexClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'drex_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  // remote fallback: the prebuilt matcher on the build host (the Mac dev box is
  // too contended to build Rust locally). Same binary, over ssh stdin.
  return { cmd: 'ssh', args: [REMOTE_HOST, `cd ${REMOTE_DIR} && ./target/debug/drex_clear`], where: REMOTE_HOST + ':' + REMOTE_DIR + ' (prebuilt, via ssh)' };
}
// fhegg-solver is a STANDALONE crate (opted out of the workspace) — its binary
// lands in its OWN target dir. LOCAL only; if not built we say so, we don't fake.
function fheggClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'fhegg-solver', 'target', prof, 'fhegg_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local fhegg-solver/target/' + prof };
  }
  return { cmd: null, args: [], where: '(not built)' };
}
// cert_f_prove is a WORKSPACE member (dregg-circuit-prove) → workspace target.
function certFProveCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'cert_f_prove');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  return { cmd: null, args: [], where: '(not built)' };
}

// Spawn an engine binary, pipe `stdinJson`, resolve the last JSON line it prints.
// A hard timeout kills a wedged child and reports honestly (never hangs the UI).
function runEngine(name, { cmd, args }, stdinJson, timeoutMs = 120_000) {
  return new Promise((resolve) => {
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '', timedOut = false;
    const timer = setTimeout(() => { timedOut = true; try { child.kill('SIGKILL'); } catch (_e) {} }, timeoutMs);
    child.stdout.on('data', d => (out += d));
    child.stderr.on('data', d => (err += d));
    child.on('error', e => { clearTimeout(timer); resolve({ ok: false, error: name + ' spawn failed: ' + e.message }); });
    child.on('close', (code) => {
      clearTimeout(timer);
      if (timedOut) return resolve({ ok: false, error: name + ' timed out after ' + timeoutMs / 1000 + 's (killed)', stderr: err.slice(-400) });
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try { resolve(JSON.parse(line)); }
      catch (_e) { resolve({ ok: false, error: name + ' produced no JSON (exit ' + code + ')', stderr: err.slice(-400), raw: out.slice(-400) }); }
    });
    child.stdin.end(stdinJson);
  });
}

// Run the REAL clear-book pipeline over the posted revealed orders.
function runClear(ordersJson) {
  return runEngine('drex_clear', drexClearCmd(), ordersJson);
}
// Run the REAL fhEgg single-phase shielded clearing over the posted orders.
function runShieldedClear(ordersJson) {
  const loc = fheggClearCmd();
  if (!loc.cmd) {
    return Promise.resolve({
      ok: false,
      error: 'fhegg_clear not built — run: cargo build --release --bin fhegg_clear  (in fhegg-solver/)',
    });
  }
  return runEngine('fhegg_clear', loc, ordersJson);
}
// Run the REAL Cert-F STARK over a solver certificate JSON. The certificate
// carries the PRIVATE witness (f, π, s); this consumes it into the STARK trace
// and returns ONLY the world-visible result — cert_f_prove never prints f/π/s.
// Proving costs SECONDS (BabyBear + FRI): a SEPARATE action, not click-latency.
function runCertFProve(certJson) {
  const loc = certFProveCmd();
  if (!loc.cmd) {
    return Promise.resolve({
      ok: false,
      error: 'cert_f_prove not built — run: cargo build --release -p dregg-circuit-prove --bin cert_f_prove',
    });
  }
  return runEngine('cert_f_prove', loc, certJson, 300_000);
}

// ── the live-node settle — faithful port of the v1 (:8781) settleOnNode ──
// (per-trader Transfer off the verified post-ledger; balances read BACK from the
// node. The Transfer-not-SetField rationale — SetField commits but is unattested
// at the deployed VK — is documented at drex-web/serve.mjs:148-167; the fix is a
// VK-epoch flip, ember-gated, correctly not fired here.)
const traderCell = (t) => crypto.createHash('sha256').update('drex-trader-v1:' + String(t)).digest('hex');
const SETTLE_CELL = 'de55e771' + '0'.repeat(56);
const felt = (n) => String(Math.max(0, Math.min(Number.MAX_SAFE_INTEGER, Math.floor(Number(n) || 0))));
async function nodeUnlock() {
  if (nodeBearer) return nodeBearer;
  const r = await fetch(NODE + '/cipherclerk/unlock', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ passphrase: NODE_PASSPHRASE }) });
  const j = await r.json();
  if (!j.success || !j.bearer_token) throw new Error('node unlock failed: ' + (j.error || r.status));
  nodeBearer = j.bearer_token; return nodeBearer;
}
async function nodeGet(p) {
  const r = await fetch(NODE + p, { headers: nodeBearer ? { Authorization: 'Bearer ' + nodeBearer } : {} });
  if (!r.ok) return { __status: r.status };
  return r.json();
}
async function nodeFaucet(cell, amount) {
  try { await fetch(NODE + '/api/faucet', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ recipient: cell, amount }) }); } catch (_e) {}
}
async function settleOnNode(cleared) {
  const bearer = await nodeUnlock();
  const ident = await nodeGet('/api/node/identity');
  const operator = ident && ident.agent_cell;
  if (!operator) throw new Error('node identity has no agent cell');
  const conserved = (cleared.conservation || []).reduce((s, c) => s + (Number(c.in) || 0), 0);
  const fills = (cleared.allocations || []).filter(a => !a.rested && Number(a.received) > 0)
    .map(a => ({ trader: String(a.trader), cell: traderCell(a.trader), recvAsset: a.recvAsset, received: Math.floor(Number(a.received)), amount: Math.max(1, Math.floor(Number(a.received))) }));
  // Devnet computron-budget envelope (a LABELED inadequacy, not a silent clamp):
  // over-ceiling batches settle scaled, surfaced via `scaled`/`scale`; the true
  // cleared `received` is kept alongside.
  const FUND_CEILING = 9000;
  const rawTotal = fills.reduce((s, f) => s + f.amount, 0);
  let scale = 1;
  if (rawTotal > FUND_CEILING) { scale = FUND_CEILING / rawTotal; for (const f of fills) f.amount = Math.max(1, Math.floor(f.amount * scale)); }
  const settledTotal = fills.reduce((s, f) => s + f.amount, 0);
  // materialize destination cells (zero-amount faucet touch; idempotent)
  const dests = fills.length ? fills.map(f => f.cell) : [SETTLE_CELL];
  await Promise.all(dests.map(c => nodeFaucet(c, 0)));
  const effects = fills.length ? fills.map(f => ({ kind: 'transfer', to: f.cell, amount: f.amount })) : [{ kind: 'transfer', to: SETTLE_CELL, amount: 1 }];
  effects.push({ kind: 'emit_event', topic: 'drex_clear_batch', data: [felt(fills.length), felt(conserved)] });
  const fee = 800 + 350 * effects.length;
  const need = fee + settledTotal + (fills.length ? 0 : 1);
  if ((ident.agent_balance || 0) < need) {
    await nodeFaucet(operator, 10000);
    const re = await nodeGet('/api/node/identity');
    if (re && (re.agent_balance || 0) < need) throw new Error(`operator underfunded (have ${re.agent_balance}, need ${need}); faucet rate-limited — retry ~1 min`);
  }
  const submit = await fetch(NODE + '/turn/submit', { method: 'POST', headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + bearer }, body: JSON.stringify({ agent: operator, nonce: 0, fee, memo: 'drex_clear', actions: [{ effects }] }) }).then(r => r.json());
  if (!submit.accepted || !submit.turn_hash) return { nodeUp: true, accepted: false, operator, error: submit.error || 'turn not accepted', submit };
  const turnHash = submit.turn_hash;
  // Poll for the async STARK proof + the committed receipt (prove_pool lands the
  // full-turn proof in ~4–15s on a --prove-turns node; poll up to ~24s).
  let proof = null, r = null;
  for (let i = 0; i < 40; i++) {
    if (!proof) { const p = await nodeGet('/api/turn/' + turnHash + '/proof'); if (p && !p.__status && p.proof_len) proof = { present: true, len: p.proof_len, mode: 'stark_full_turn' }; }
    const recs = await nodeGet('/api/starbridge/receipts?turn_hash=' + turnHash);
    if (Array.isArray(recs) && recs.length) r = recs[0].receipt || recs[0];
    if (proof || (r && (r.witness_count > 0 || r.has_proof))) break;
    await new Promise(x => setTimeout(x, 600));
  }
  if (!proof && r && (r.witness_count > 0 || r.has_proof)) proof = { present: true, len: null, mode: 'witnessed_receipt', witnessCount: r.witness_count };
  const proofNote = proof ? null : 'prove_pool enqueued the async STARK job; no proof attached yet (committed-but-unattested)';
  const cell = await nodeGet('/api/cell/' + operator);
  // Read each trader's cell balance back FROM the node — the per-trader
  // allocation is a real ledger state change, not a synthesized number.
  const perTrader = await Promise.all(fills.map(async (f) => {
    const tc = await nodeGet('/api/cell/' + f.cell);
    return {
      trader: f.trader, cell: f.cell, recvAsset: f.recvAsset,
      received: f.received,          // the true cleared amount (drex_clear post-ledger)
      settled: f.amount,             // the computrons transferred this settle (== received unless scaled)
      balance: tc && !tc.__status && tc.found ? tc.balance : null,
    };
  }));
  return {
    nodeUp: true, accepted: true, node: NODE, operator, turnHash,
    proofStatus: submit.proof_status, witnessCount: submit.witness_count,
    proof: proof || { present: false }, proofNote,
    settle: { mode: 'per_trader_transfer', traders: fills.length, settledTotal, scaled: scale < 1, scale: Number(scale.toFixed(6)) },
    perTrader,
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

// ── static + routing ──
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.mjs': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json', '.map': 'application/json', '.svg': 'image/svg+xml' };
function send(res, code, body, type) { res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache' }); res.end(body); }
function readBody(req) { return new Promise((resolve) => { let b = ''; req.on('data', c => { b += c; if (b.length > 1 << 20) req.destroy(); }); req.on('end', () => resolve(b)); }); }

// Validate an orders POST body before shelling to an engine: must be a JSON
// array of order-shaped objects. Rejecting garbage here gives the UI a crisp
// 400 instead of an opaque engine parse error (and never spawns on junk).
function parseOrders(body) {
  let orders;
  try { orders = JSON.parse(body); } catch (_e) { return { error: 'body is not valid JSON' }; }
  if (!Array.isArray(orders) || orders.length === 0) return { error: 'expected a non-empty JSON array of orders' };
  for (const [i, o] of orders.entries()) {
    if (!o || typeof o !== 'object') return { error: `order[${i}] is not an object` };
    if (!o.trader || typeof o.trader !== 'string') return { error: `order[${i}] missing trader` };
    if (!(Number(o.offerAmount) > 0)) return { error: `order[${i}] (${o.trader}) offerAmount must be > 0` };
    if (!(Number(o.wantMin) >= 0)) return { error: `order[${i}] (${o.trader}) wantMin must be ≥ 0` };
    if (!o.offerAsset || !o.wantAsset) return { error: `order[${i}] (${o.trader}) missing offer/want asset` };
  }
  return { orders };
}

async function route(req, res, url) {
  // ── POST /clear — the REAL matcher (solver.rs + verified_settle.rs) ──
  if (req.method === 'POST' && url === '/clear') {
    const body = await readBody(req);
    const v = parseOrders(body);
    if (v.error) return send(res, 400, JSON.stringify({ ok: false, error: v.error }), MIME['.json']);
    const result = await runClear(JSON.stringify(v.orders));
    return send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
  }

  // ── POST /clear-shielded — the REAL fhEgg single-phase shielded clearing ──
  // (fhegg-solver: PDHG circulation + Cert-F certificate + the verified AIR gate).
  if (req.method === 'POST' && url === '/clear-shielded') {
    const body = await readBody(req);
    const v = parseOrders(body);
    if (v.error) return send(res, 400, JSON.stringify({ ok: false, error: v.error }), MIME['.json']);
    const result = await runShieldedClear(JSON.stringify(v.orders));
    return send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
  }

  // ── POST /prove-shielded — the REAL reveal-nothing STARK (SEPARATE action) ──
  // Runs the SAME batch through fhegg_clear to get the SOLVER's plaintext
  // certificate (the private witness f/π/s), then proves it in the REAL dregg
  // STARK. The browser response carries ONLY what the world may see — never
  // f/π/s. The solver certificate stays SERVER-SIDE; the redaction is structural
  // (we build the world-view field-by-field; `cleared` is never spread).
  if (req.method === 'POST' && url === '/prove-shielded') {
    const body = await readBody(req);
    const v = parseOrders(body);
    if (v.error) return send(res, 400, JSON.stringify({ ok: false, error: v.error }), MIME['.json']);
    // [1] SOLVER view (server-side): clear the batch, obtain the Cert-F certificate.
    const cleared = await runShieldedClear(JSON.stringify(v.orders));
    if (cleared.error || !cleared.solverCert) {
      return send(res, 502, JSON.stringify({
        ok: false, stage: 'clear',
        error: cleared.error || 'fhegg_clear did not emit solverCert (rebuild fhegg_clear)',
        stderr: cleared.stderr,
      }), MIME['.json']);
    }
    const cert = cleared.solverCert; // holds f, π, s — SERVER-SIDE ONLY, never sent on.
    // [2] PROVE (server-side): the witness is consumed into the trace.
    const prove = await runCertFProve(JSON.stringify(cert));
    if (!prove.ok) {
      return send(res, 502, JSON.stringify({ ok: false, stage: 'prove', error: prove.error, stderr: prove.stderr }), MIME['.json']);
    }
    // [3] WORLD view: the prover's output + PUBLIC clearing scalars only.
    const conserves = !!(cleared.certificate && cleared.certificate.conserves);
    const worldView = {
      ok: true,
      verify: prove.verify,
      proofBytes: prove.proofBytes,
      clearedVolume: prove.clearedVolume,   // the public input wᵀf
      publicInputs: prove.publicInputs,     // the STARK's exposed field elements = [wᵀf]
      program: { nodes: prove.nNodes, edges: prove.mEdges, epsilon: prove.epsilon, scale: prove.scale },
      conserves,
      trace: { width: prove.traceWidth, valueBits: prove.valueBits },
      descriptor: prove.descriptor,
      proveMs: prove.proveMs,
      verifyMs: prove.verifyMs,
      hides: prove.hides,
      redaction: prove.note,
      remaining: {
        noteCommitmentMatching: 'the demo still takes REVEALED orders as input; matching over HIDDEN NOTE COMMITMENTS (the shielded pool, shielded_ring_clears) is the input-privacy lane',
        zkFloor: 'reveal-nothing rests on the STARK ZK: the HidingFriPcs statistical-ZK floor (Market/RevealNothing.lean — reveal_law is HidingFriPcs-conditional, like the linking tower is HashCR-conditional)',
      },
    };
    return send(res, 200, JSON.stringify(worldView), MIME['.json']);
  }

  // ── GET /node/status — is a live dregg node reachable? ──
  if (req.method === 'GET' && url === '/node/status') {
    try { const r = await fetch(NODE + '/status'); return send(res, 200, JSON.stringify({ up: true, node: NODE, status: await r.json() }), MIME['.json']); }
    catch (e) { return send(res, 200, JSON.stringify({ up: false, node: NODE, error: e.message }), MIME['.json']); }
  }

  // ── GET /engines — honest live-surface report (which binaries back which routes) ──
  if (req.method === 'GET' && url === '/engines') {
    return send(res, 200, JSON.stringify(engineReport()), MIME['.json']);
  }

  // ── POST /settle — land the cleared batch as ONE real turn on the live node ──
  if (req.method === 'POST' && url === '/settle') {
    let cleared; try { cleared = JSON.parse(await readBody(req)); } catch (_e) { return send(res, 400, JSON.stringify({ error: 'bad json' }), MIME['.json']); }
    try { return send(res, 200, JSON.stringify(await settleOnNode(cleared)), MIME['.json']); }
    catch (e) { return send(res, 200, JSON.stringify({ nodeUp: false, node: NODE, error: e.message }), MIME['.json']); }
  }

  // static — v2 dir only, plus the reused drex-viz from the sibling drex-web/
  // (the bundle inlines it, but allow direct source serving for the no-build
  // dev path). No path escape outside the repo.
  const file = path.join(HERE, url);
  if (!path.resolve(file).startsWith(REPO)) return send(res, 403, 'forbidden');
  fs.readFile(file, (err, buf) => {
    if (err) return send(res, 404, 'not found: ' + url);
    send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream');
  });
}

// The honest engine/status report (shared by /engines and --check): which REAL
// binary backs each route right now, and which routes will answer with the
// honest not-built fallback.
function engineReport() {
  const clear = drexClearCmd(), fhegg = fheggClearCmd(), certf = certFProveCmd();
  return {
    clear:         { route: 'POST /clear',          engine: 'drex_clear',   where: clear.where, ready: true, note: clear.cmd === 'ssh' ? 'no local binary — will shell to the build host over ssh' : null },
    clearShielded: { route: 'POST /clear-shielded', engine: 'fhegg_clear',  where: fhegg.where, ready: !!fhegg.cmd, note: fhegg.cmd ? null : 'not built — the route answers with the honest build instruction' },
    proveShielded: { route: 'POST /prove-shielded', engine: 'fhegg_clear → cert_f_prove', where: certf.where, ready: !!fhegg.cmd && !!certf.cmd, note: certf.cmd ? null : 'cert_f_prove not built — the route answers with the honest build instruction' },
    settle:        { route: 'POST /settle',         engine: 'live dregg node', where: NODE, ready: null, note: 'probed at runtime; { nodeUp:false } fallback when unreachable' },
  };
}

if (CHECK) {
  // ── no-listen self-check: what would this server actually serve? ──
  let bad = 0;
  const statics = ['index.html', 'styles.css', path.join('dist', 'app.js')];
  for (const f of statics) {
    const ok = fs.existsSync(path.join(HERE, f));
    if (!ok) bad++;
    console.log(`${ok ? ' ok ' : 'MISS'}  static  ${f}${!ok && f.endsWith('app.js') ? '   → run: npm run build' : ''}`);
  }
  const rep = engineReport();
  for (const k of Object.keys(rep)) {
    const e = rep[k];
    const state = e.ready === true ? ' ok ' : e.ready === false ? 'FALL' : 'RUN ';
    console.log(`${state}  ${e.route}  → ${e.engine} @ ${e.where}${e.note ? '   (' + e.note + ')' : ''}`);
  }
  try {
    const r = await fetch(NODE + '/status', { signal: AbortSignal.timeout(1500) });
    console.log(` ok   node ${NODE} reachable (status ${r.status})`);
  } catch (_e) {
    console.log(`FALL  node ${NODE} unreachable — /settle answers { nodeUp:false } (honest fallback)`);
  }
  console.log(bad ? `\n--check: ${bad} static asset(s) missing` : '\n--check: static surface complete; fallbacks above are honest, not failures');
  process.exit(bad ? 1 : 0);
}

http.createServer((req, res) => {
  const url = decodeURIComponent(req.url.split('?')[0]) === '/' ? '/index.html' : decodeURIComponent(req.url.split('?')[0]);
  route(req, res, url).catch((e) => send(res, 500, JSON.stringify({ error: 'internal: ' + e.message }), MIME['.json']));
}).listen(PORT, HOST, () => {
  console.log('DrEX v2 terminal → http://' + HOST + ':' + PORT);
  console.log('  REAL matcher   POST /clear           → drex_clear @ ' + drexClearCmd().where);
  console.log('  SHIELDED clear POST /clear-shielded  → fhegg_clear @ ' + fheggClearCmd().where);
  console.log('  REVEAL-NOTHING POST /prove-shielded  → cert_f_prove @ ' + certFProveCmd().where);
  console.log('  LIVE node      POST /settle          → ' + NODE + '   (GET /node/status probes it)');
  console.log('  build the app first:  npm run build   (esbuild → dist/app.js)');
});
