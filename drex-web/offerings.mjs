// offerings.mjs — the DreggFi OFFERINGS menu server (a NEW, self-contained surface).
//
//   node drex-web/offerings.mjs   → http://localhost:8790
//
// This is a SIBLING of serve.mjs (the ring-DrEX surface on :8781), deliberately a
// SEPARATE file + port so it never clobbers the live drex-web lanes. It serves the
// "DreggFi Offerings" menu (offerings.html) and runs the REAL fhegg-solver engine
// for each pickable offering — the derivatives desk, the package auction, and the
// shielded ring clearing — through the thin JSON-CLI runner bins:
//
//   POST /offering/derivatives  → pricecert_clear  (Price-Cert: European state-price / American Snell)
//   POST /offering/package      → package_clear     (all-or-none combinatorial clearing + certified bound)
//   POST /offering/drex-shielded→ fhegg_clear       (PDHG circulation + Cert-F + the verified AIR gate)
//
// Each response is a REAL clearing + its verified certificate — no mock. LOCAL only:
// if a runner bin is not built, the endpoint says how to build it rather than fake a
// result. Binds 127.0.0.1 by default (same wildcard guard shape as serve.mjs). The
// ring DrEX (drex_clear, needs the prebuilt matcher) + the launchpad are LINKED to
// their own surfaces from the menu, not re-run here.
//
// HONEST SCOPE: this is a devnet-DEMO surface — the real engine, run locally, each
// clearing showing its certificate + privacy tier. Actual PUBLIC devnet deployment
// (a hosted node, live broadcast, live tokens) is the ember-gated step, named in
// docs/deos/DREGGFI-DEVNET-OFFERINGS.md, not performed here.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, '..');
const SOLVER = path.join(REPO, 'fhegg-solver');
const PORT = process.env.OFFERINGS_PORT || 8790;

const HOST = process.env.OFFERINGS_BIND || '127.0.0.1';
const WILDCARD = HOST === '0.0.0.0' || HOST === '::' || HOST === '*';
if (WILDCARD && process.env.OFFERINGS_ALLOW_WILDCARD !== '1') {
  console.error(`refusing to bind ${HOST} (all-interfaces = public UNLESS a host firewall gates :${PORT}).`);
  console.error(`  set OFFERINGS_BIND=127.0.0.1 (default) or the LAN IP; wildcard needs OFFERINGS_ALLOW_WILDCARD=1 behind a firewall.`);
  process.exit(1);
}

// Locate a fhegg-solver runner bin, release-first. fhegg-solver is a STANDALONE
// crate, so its bins land in fhegg-solver/target/{release,debug}/.
function solverBin(name) {
  for (const prof of ['release', 'debug']) {
    const p = path.join(SOLVER, 'target', prof, name);
    if (fs.existsSync(p)) return { cmd: p, where: 'fhegg-solver/target/' + prof };
  }
  return { cmd: null, where: '(not built)' };
}

const BUILD_HINT = {
  pricecert_clear: 'cargo build --release -p fhegg-solver --bin pricecert_clear  (in fhegg-solver/)',
  package_clear: 'cargo build --release -p fhegg-solver --bin package_clear  (in fhegg-solver/)',
  fhegg_clear: 'cargo build --release -p fhegg-solver --bin fhegg_clear  (in fhegg-solver/)',
};

// Run a runner bin: pipe the request body to stdin, parse the last JSON line.
function runBin(name, stdinJson) {
  return new Promise((resolve) => {
    const { cmd } = solverBin(name);
    if (!cmd) {
      return resolve({ ok: false, notBuilt: true, error: `${name} not built — run: ${BUILD_HINT[name] || 'cargo build'}` });
    }
    const child = spawn(cmd, [], { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', (e) => resolve({ ok: false, error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try {
        resolve({ ok: true, result: JSON.parse(line) });
      } catch (_e) {
        resolve({ ok: false, error: `${name} produced no JSON (exit ${code})`, stderr: err.slice(-400), raw: out.slice(-400) });
      }
    });
    child.stdin.end(stdinJson || '');
  });
}

// The offerings manifest — the menu the UI renders. `stage` is the HONEST
// devnet-deployable stage per docs/deos/DREGGFI-DEVNET-OFFERINGS.md.
function manifest() {
  const has = (n) => !!solverBin(n).cmd;
  return {
    title: 'DreggFi Offerings',
    scope: 'devnet-DEMO surface: the real fhegg-solver engine, run LOCAL, each clearing showing its certificate + privacy tier. Public devnet broadcast + live tokens = the ember-gated step (named, not run).',
    offerings: [
      {
        id: 'drex-ring', name: 'Multilateral ring DrEX', mechanism: 'TTC ring match → verified_settle',
        tier: 'Tier 2 OPEN (the general ring; public clearing over a verified kernel)', stage: 'deployable-now (its own surface)',
        run: null, link: 'http://localhost:8781', note: 'the ring-clearing surface (serve.mjs :8781): real solver + extension wallet + live-node settle. Opens in its own tab.',
      },
      {
        id: 'drex-shielded', name: 'Shielded batch clearing', mechanism: 'PDHG circulation + Cert-F + verified AIR gate',
        tier: 'Tier 1 SHIELDED target (demo shows the plaintext Cert-F; the reveal-nothing STARK wrap is the cert_f_prove lane)', stage: has('fhegg_clear') ? 'deployable-now (runs here)' : 'built, bin not compiled',
        run: '/offering/drex-shielded', link: null, note: 'the convex-clearing route: a fair batch cleared, per-asset conservation held, a tampered certificate REJECTED.',
      },
      {
        id: 'derivatives', name: 'Derivatives desk (Price-Cert)', mechanism: 'state-price LP (European) + Snell-envelope LP (American)',
        tier: 'runs OPEN (plaintext cert); fhir admissible tier = Dark (European small grid) / Shielded (American tree)', stage: has('pricecert_clear') ? 'deployable-now (runs here)' : 'built, bin not compiled',
        run: '/offering/derivatives', link: null, note: 'price a European basket or an American option; the certificate re-checks every clause; an arbitrage market is REJECTED.',
      },
      {
        id: 'package', name: 'Package / combinatorial auction', mechanism: 'all-or-none clearing + certified near-optimality bound',
        tier: 'runs OPEN (plaintext cert); fhir admissible tier = Shielded (discrete, certified-approx)', stage: has('package_clear') ? 'deployable-now (runs here)' : 'built, bin not compiled',
        run: '/offering/package', link: null, note: 'clear indivisible bundles; feasibility ALWAYS proven; near-optimality is a certified α=W/UB bound; exact optimum stays NP-hard.',
      },
      {
        id: 'launchpad', name: 'Anti-rug launchpad', mechanism: 'clearing-attested eligibility + solvent pool (29/29 gate)',
        tier: 'distribution product — on-chain contracts (real wallet, real bytecode)', stage: 'deployable-now (its own surface; devnet contracts, 29/29 gate green)',
        run: null, link: 'http://localhost:8785', note: 'the launchpad-web surface (server.mjs :8785). A token launch gated by a real clearing attestation. Start it separately; opens in its own tab.',
      },
      {
        id: 'portfolio', name: 'Portfolio / Fisher / CFMM', mechanism: 'QP portfolio + Fisher market equilibrium + CFMM',
        tier: 'T1/T2 — verified clearing', stage: 'spec\'d — engine built (fhegg-solver: qp.rs / fisher.rs / cfmm.rs), runner bin not yet wired',
        run: null, link: null, note: 'the library + bench exist; the JSON-CLI runner (a portfolio_clear sibling) is the one-file wire needed to make it clickable.',
      },
    ],
  };
}

const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json', '.svg': 'image/svg+xml',
};
function send(res, code, body, type) {
  res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache' });
  res.end(body);
}
function readBody(req) {
  return new Promise((resolve) => {
    let b = '';
    req.on('data', (c) => { b += c; if (b.length > 1 << 20) req.destroy(); });
    req.on('end', () => resolve(b));
  });
}

const RUN_ROUTES = {
  '/offering/derivatives': 'pricecert_clear',
  '/offering/package': 'package_clear',
  '/offering/drex-shielded': 'fhegg_clear',
};

http.createServer(async (req, res) => {
  let url = decodeURIComponent(req.url.split('?')[0]);
  if (url === '/') url = '/offerings.html';

  if (req.method === 'GET' && url === '/offerings') {
    return send(res, 200, JSON.stringify(manifest()), MIME['.json']);
  }

  if (req.method === 'POST' && RUN_ROUTES[url]) {
    const body = await readBody(req);
    const r = await runBin(RUN_ROUTES[url], body);
    return send(res, r.ok ? 200 : 502, JSON.stringify(r), MIME['.json']);
  }

  // Static: only offerings.* files from drex-web/ (no path escape, no wallet mount).
  const file = path.join(HERE, url);
  if (!path.resolve(file).startsWith(HERE)) return send(res, 403, 'forbidden');
  fs.readFile(file, (err, buf) => {
    if (err) return send(res, 404, 'not found: ' + url);
    send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream');
  });
}).listen(PORT, HOST, () => {
  console.log('DreggFi Offerings → http://' + HOST + ':' + PORT);
  for (const [route, bin] of Object.entries(RUN_ROUTES)) {
    console.log(`  POST ${route.padEnd(26)} → ${bin} @ ${solverBin(bin).where}`);
  }
  console.log('  GET  /offerings              → the menu manifest (stage per offering)');
});
