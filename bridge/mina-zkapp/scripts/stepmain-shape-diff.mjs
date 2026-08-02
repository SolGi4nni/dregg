// STEP_MAIN SHAPE DIFF — the Lean-assembled `verify_one` against Mina's own compiled step circuit.
//
// WHAT THIS IS, AND WHAT IT IS NOT. `mina-canonical-circuit-oracle.mjs` establishes that o1-labs'
// `*_gates.json` release blobs ARE Mina's canonical circuits (its digest reproduces the md5 in
// o1-labs' own asset filename). This script uses one of those blobs as a SHAPE ORACLE for
// `Dregg2.Circuit.Emit.KimchiStepMain`: it compares the gate-type HISTOGRAM and, more importantly,
// the RUN-LENGTH profile of each gate family.
//
// ⚠ It is NOT a byte requirement and it is NOT green-or-bust. The step circuit is ours to author
// (wrap is per-zkApp; `wrap_main` bakes the step VK in as circuit constants, so no canonical-wrap
// check exists and there is no reproduction target). What the run lengths ARE is a cheap, early
// signal that a GADGET was mis-assembled: a Poseidon permutation is 11 rows, a 128-bit
// `Scalar_challenge.endo` is 32 `EndoMul` rows, a `var_base_mul` chunk is a lone `VarBaseMul` row
// followed by its `Zero`, and a 128-bit `to_field_checked` is 8 `EndoMulScalar` rows. A divergence
// there is a defect; a divergence in COUNT is a scope statement, not a defect — read the
// "named simplifications" list in the Lean module header before calling one a bug.
//
// USAGE
//   node scripts/mina-canonical-circuit-oracle.mjs --circuit step-zkapp-proved --dump /tmp/mina.json
//   DREGG_SM=step lake env lean --run Dregg2/Circuit/Emit/EmitStepMainJson.lean   # (in metatheory/)
//   node scripts/stepmain-shape-diff.mjs /tmp/mina.json /tmp/pickles-stepmain/stepmain_step_r5_full.json
//
// `step-zkapp-proved` is step branch 4 — the branch that RUNS `verify_one` on a side-loaded proof.
// `step-transaction` (branch 0) is instantiated with N_PREVIOUS = 0 and contains NO `verify_one`
// call at all (mina-rust `transaction.rs:4286`), so it is the wrong reference for this comparison.
import { readFileSync } from 'node:fs';

// GateType declaration order == the BCS variant index (kimchi `circuits/gate.rs`). Only these seven
// appear in ANY Mina step or wrap circuit — no lookup, no foreign-field, no range-check.
const NAMES = ['Zero', 'Generic', 'Poseidon', 'CompleteAdd', 'VarBaseMul', 'EndoMul', 'EndoMulScalar'];

/** The oracle's `--dump` shape: `gate_list` entries carry a string `typ`. */
function loadMina(p) {
  const j = JSON.parse(readFileSync(p, 'utf8'));
  if (!j.gate_list) throw new Error(`${p}: no gate_list — dump it with the oracle's --dump flag`);
  return { name: j.circuit, pub: j.public_input_size, gates: j.gate_list.map((g) => g.typ) };
}

/** The Lean emitter's shape: `gates[i].typ` is the ORDINAL. */
function loadLean(p) {
  const j = JSON.parse(readFileSync(p, 'utf8'));
  return { name: j.name, pub: j.public_input_size, gates: j.gates.map((g) => NAMES[g.typ]) };
}

const histogram = (gs) => gs.reduce((h, g) => ((h[g] = (h[g] ?? 0) + 1), h), {});

/** Run lengths of one gate family, as `<len>x<count>` ordered by count. This is the fidelity signal. */
function runLengths(gs, kind) {
  const runs = [];
  let n = 0;
  for (const g of gs) {
    if (g === kind) n++;
    else if (n) { runs.push(n); n = 0; }
  }
  if (n) runs.push(n);
  const c = {};
  for (const x of runs) c[x] = (c[x] ?? 0) + 1;
  return Object.entries(c).sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k}x${v}`).join(' ');
}

function report(c) {
  const h = histogram(c.gates);
  const tot = c.gates.length;
  console.log(`\n=== ${c.name} — ${tot} gates, public_input_size ${c.pub} ===`);
  for (const k of NAMES) {
    if (!h[k]) continue;
    console.log(`   ${k.padEnd(14)} ${String(h[k]).padStart(6)}  ${(100 * h[k] / tot).toFixed(1)}%`);
  }
  console.log(`   ${'non-Generic'.padEnd(14)} ${String(tot - (h.Generic ?? 0)).padStart(6)}`);
  for (const k of ['Poseidon', 'EndoMul', 'EndoMulScalar', 'VarBaseMul', 'CompleteAdd']) {
    if (h[k]) console.log(`   runlen ${k.padEnd(14)} ${runLengths(c.gates, k)}`);
  }
  const unknown = new Set(c.gates.filter((g) => !NAMES.includes(g)));
  if (unknown.size) console.log(`   ⚠ gate types outside the seven: ${[...unknown].join(', ')}`);
}

const [minaPath, ...leanPaths] = process.argv.slice(2);
if (!minaPath || leanPaths.length === 0) {
  console.error('usage: node stepmain-shape-diff.mjs <mina-dump.json> <lean-circuit.json>...');
  process.exit(2);
}
report(loadMina(minaPath));
for (const p of leanPaths) report(loadLean(p));
console.log(
  '\nRead the RUN LENGTHS first: a mismatch there is a mis-assembled gadget. A count shortfall is a\n'
  + 'scope statement — check the named-simplifications list in KimchiStepMain.lean before calling it a bug.',
);
