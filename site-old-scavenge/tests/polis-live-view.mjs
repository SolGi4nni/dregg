/**
 * LIVE-VIEW seam closure test: a LIVE council cell self-describes its
 * threshold M through the served program view.
 *
 * This is the e2e for the StateConstraintView totality close:
 *
 *   1. boot the REAL wasm runtime (site/pkg — rebuild via
 *      `wasm-pack build wasm --target web --out-dir pkg --release` +
 *      `cp -R wasm/pkg/. site/pkg/` if stale),
 *   2. deploy the GENERATED council factory descriptor (the same 2-of-3
 *      charter the Rust constructors produce),
 *   3. mint a live cell from it,
 *   4. read `get_cell_state(...).program` — the served view — and
 *   5. decode threshold M from the AffineLe projection with the SAME
 *      `classifyConstraints` the polis inspector uses.
 *
 * Before the totality close, step 5 was impossible: AffineLe/MemberOf had no
 * StateConstraintView projection, the inspector rendered "/ M (not in node
 * view)", and polis-inspector.mjs pinned `thresholdInData === false`.
 *
 * Run: node site/tests/polis-live-view.mjs
 * Requires http://localhost:4818 serving the built site (dist).
 */
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from '../node_modules/playwright/index.mjs';

const SITE = path.dirname(path.dirname(fileURLToPath(import.meta.url)));
const STUDIO = path.join(SITE, 'src', '_includes', 'studio');
const BASE = 'http://localhost:4818';

const { classifyConstraints, constraintsOf } =
  await import(path.join(STUDIO, 'polis-decode.js'));

const samples = JSON.parse(
  fs.readFileSync(path.join(STUDIO, 'factory-samples.generated.json'), 'utf8'));

// The descriptor-side truth to compare the live view against.
const descriptorCls = classifyConstraints(constraintsOf(samples.council.descriptor));
if (!descriptorCls || descriptorCls.threshold == null) {
  console.error('FAIL: council sample descriptor did not decode a threshold (fixture problem)');
  process.exit(1);
}

async function run() {
  const browser = await chromium.launch({ headless: true });
  const page = await (await browser.newContext()).newPage();
  const pageErrors = [];
  page.on('pageerror', (e) => pageErrors.push(e.message));

  await page.goto(`${BASE}/studio`, { waitUntil: 'domcontentloaded' });

  // Drive the RAW wasm module — no studio shims — so the test pins the
  // actual served shape.
  const served = await page.evaluate(async (descriptorJson) => {
    const wasm = await import('/pkg/dregg_wasm.js');
    await wasm.default();
    const h = wasm.create_runtime();
    // Genesis first (factories need a signer), then the council from its factory.
    wasm.create_agent(h, 'genesis', 1000000n);
    const dep = wasm.deploy_factory_descriptor(h, descriptorJson);
    const born = wasm.create_agent_with_factory(h, 'council', 0n, dep.factory_vk);
    const state = wasm.get_cell_state(h, born.cell_id);
    // BigInt-safe transport back to node.
    return JSON.parse(JSON.stringify(
      { cell_id: born.cell_id, program: state.program, fields: state.fields },
      (_k, v) => (typeof v === 'bigint' ? Number(v) : v),
    ));
  }, JSON.stringify(samples.council.descriptor));

  await browser.close();

  let failures = 0;
  const check = (cond, what) => {
    if (!cond) { console.error(`FAIL: ${what}`); failures++; }
    else console.log(`ok: ${what}`);
  };

  check(pageErrors.length === 0, `no page errors (got: ${pageErrors.join(' | ')})`);
  check(served.program && served.program.kind === 'Predicate',
    `live cell serves a Predicate program view (got ${served.program?.kind})`);

  const constraints = constraintsOf(served.program);
  const affine = constraints.find((c) => c && c.kind === 'AffineLe');
  check(!!affine, 'served view carries the AffineLe threshold gate (the projection is total)');
  check(Array.isArray(affine?.terms) && affine.terms.length > 0,
    'AffineLe view carries its terms (coefficients + slots)');

  // The SAME decode the inspector does — against the LIVE view.
  const cls = classifyConstraints(constraints);
  check(cls && (cls.family === 'council' || cls.family === 'amendment'),
    `live view classifies as a council family (got ${cls?.family})`);
  check(cls?.thresholdInData === true,
    'LIVE cell carries M in data (thresholdInData === true — the seam is closed)');
  check(cls?.threshold === descriptorCls.threshold,
    `live threshold M === descriptor M (${cls?.threshold} vs ${descriptorCls.threshold})`);
  check(cls?.members === descriptorCls.members,
    `live member count === descriptor member count (${cls?.members} vs ${descriptorCls.members})`);

  if (failures) { console.error(`\n${failures} failure(s)`); process.exit(1); }
  console.log('\nlive council cell self-describes its threshold M — seam closed');
}

run().catch((e) => { console.error('FAIL (harness):', e); process.exit(1); });
