// MINA PROOF VERIFY GATE — hand a (proof, verification key) pair to MINA'S OWN VERIFIER and report
// what it says, literally.
//
// ## Why this file exists
//
// The tree already had the two halves and not the join:
//
//   * `mina-vk-parse-gate.mjs`   — does Mina's own reader PARSE a key we derived?      (yes, 1796 B)
//   * `mina-proof-parse-gate.mjs`— does Mina's own reader PARSE a proof we encoded?    (yes)
//
// Parsing is not verifying. Neither gate consults a key while reading a proof, and neither runs a
// single field operation of the actual check. This one does: it calls o1js's `verify(proof, vk)`,
// which is `Pickles.verify(statement, picklesProof, vkBase64)` — Mina's OCaml Pickles verifier
// compiled into o1js (`o1js/dist/node/lib/proof-system/zkprogram.js:63-83`). Whatever it returns or
// throws is the answer, and this script prints it verbatim.
//
// ## ⚑ The control is not optional
//
// A script that only ever prints `false` proves nothing about the artifact under test — it is
// equally consistent with a broken harness. So every run starts with a KNOWN-GOOD pair (an o1js
// proof and the key of the program that produced it, both already in `.fullchain/`) and REFUSES to
// report on anything else unless that pair returns `true`. And it runs the known-good proof against
// a FOREIGN key, which must not return `true`, so the gate is shown to discriminate in both
// directions before it is believed about ours.
//
// ## Usage
//
//   node scripts/mina-proof-verify-gate.mjs \
//     --pair <label> <proof.json> <vk.json>   [--pair …]
//
// A `<proof.json>` is o1js's own `Proof.toJSON()` shape:
//   { publicInput: string[], publicOutput: string[], maxProofsVerified: 0|1|2, proof: "<base64>" }
// A `<vk.json>` is `{ data: "<base64>", hash: "<decimal>" }`; extra keys ignored. `--vk-data` takes
// the base64 directly.
//
// Exit status is 0 when the controls behaved and every pair produced a VERDICT (true, false, or a
// named error). It is 1 only when the controls themselves failed — i.e. when the gate cannot be
// believed. A `false` on a pair under test is a RESULT, not a harness failure, and this script
// deliberately does not conflate the two.

import { readFileSync, existsSync } from 'node:fs';
import { pathToFileURL, fileURLToPath } from 'node:url';
import path from 'node:path';

// o1js's package `exports` map hides `dist/node/...`; resolve the package directory by walking up,
// exactly as the two parse gates do.
const O1JS = (() => {
  let d = path.dirname(fileURLToPath(import.meta.url));
  for (;;) {
    const c = path.join(d, 'node_modules', 'o1js');
    if (existsSync(path.join(c, 'dist', 'node', 'index.js'))) return c;
    const up = path.dirname(d);
    if (up === d) throw new Error('cannot locate node_modules/o1js above ' + import.meta.url);
    d = up;
  }
})();
const imp = (p) => import(pathToFileURL(path.join(O1JS, p)).href);

const o1js = await imp('dist/node/index.js');
const bindings = await imp('dist/node/bindings.js');
await bindings.initializeBindings();
if (typeof o1js.verify !== 'function') {
  throw new Error('o1js did not export `verify`; refusing to run a gate that cannot go green');
}

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO_MINA = path.resolve(HERE, '..');

const readJson = (p) => JSON.parse(readFileSync(p, 'utf8'));
const vkDataOf = (p) => {
  const v = readJson(p);
  if (typeof v.data !== 'string') throw new Error(`${p}: no base64 \`data\` field`);
  return v.data;
};

/**
 * One call into Mina's verifier. Returns a VERDICT record; it never throws, because a throw from
 * Pickles is exactly the thing this gate exists to report.
 */
async function verdict(label, proofJson, vkData) {
  const t0 = Date.now();
  try {
    const ok = await o1js.verify(proofJson, vkData);
    return { label, kind: 'returned', value: ok, ms: Date.now() - t0 };
  } catch (e) {
    const msg = e && e.message ? String(e.message) : String(e);
    return { label, kind: 'threw', value: msg, ms: Date.now() - t0 };
  }
}

const show = (v) => {
  if (v.kind === 'returned') {
    console.log(`  ${v.label}: o1js verify() RETURNED ${v.value}   (${v.ms} ms)`);
  } else {
    console.log(`  ${v.label}: o1js verify() THREW   (${v.ms} ms)`);
    for (const line of v.value.split('\n')) console.log(`      | ${line}`);
  }
};

// ---------------------------------------------------------------- argv
const argv = process.argv.slice(2);
const pairs = [];
for (let i = 0; i < argv.length; i++) {
  if (argv[i] === '--pair') {
    const label = argv[++i];
    const proof = argv[++i];
    const vk = argv[++i];
    if (!label || !proof || !vk) throw new Error('--pair wants <label> <proof.json> <vk.json>');
    pairs.push({ label, proof, vk });
  } else throw new Error('unknown argument ' + argv[i]);
}

// ---------------------------------------------------------------- controls
// A proof o1js itself produced, and the key of the program that produced it. Both committed.
const CTRL_PROOF = path.join(REPO_MINA, '.fullchain', 'fold-root-proof.json');
const CTRL_VK = path.join(REPO_MINA, '.fullchain', 'fold-fold-vk.json');
const FOREIGN_VK = path.join(REPO_MINA, '.fullchain', 'pasta-braid-vk-0.json');

console.log('MINA PROOF VERIFY GATE — o1js `verify(proof, vk)` = Pickles.verify, Mina\'s own OCaml');
console.log(`  o1js       : ${O1JS}`);
console.log('\n[controls] the gate must be shown to move in both directions before it is believed');

if (!existsSync(CTRL_PROOF) || !existsSync(CTRL_VK)) {
  console.log(`  MISSING control fixtures (${CTRL_PROOF} / ${CTRL_VK}) — refusing to report`);
  process.exit(1);
}

const green = await verdict('known-good pair (o1js proof + its own key)', readJson(CTRL_PROOF), vkDataOf(CTRL_VK));
show(green);
const red = await verdict('same proof, FOREIGN key', readJson(CTRL_PROOF), vkDataOf(FOREIGN_VK));
show(red);

const controlsOk = green.kind === 'returned' && green.value === true && !(red.kind === 'returned' && red.value === true);
console.log(`  controls: ${controlsOk ? 'OK — green is reachable and a foreign key does not pass' : 'BROKEN'}`);
if (!controlsOk) {
  console.log('  refusing to report on the pairs under test: a verdict from a gate that cannot go green means nothing');
  process.exit(1);
}

// ---------------------------------------------------------------- the pairs under test
console.log('\n[under test]');
for (const p of pairs) {
  const proofJson = readJson(p.proof);
  console.log(`  --- ${p.label}`);
  console.log(`      proof: ${p.proof}  (maxProofsVerified=${proofJson.maxProofsVerified}, |publicInput|=${(proofJson.publicInput ?? []).length}, |publicOutput|=${(proofJson.publicOutput ?? []).length})`);
  console.log(`      vk   : ${p.vk}`);
  show(await verdict(p.label, proofJson, vkDataOf(p.vk)));
}

console.log('\nEvery line above is what Mina\'s own verifier said. Nothing here is interpreted.');
