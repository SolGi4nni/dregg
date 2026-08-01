// R1 custom-gate BYTE-DIFF — o1js's emitted custom-gate rows vs the Lean emitter's.
//
// MIGRATED to the shared `diff-oracle.mjs` harness (shape `gates`): the core diff is the 165 poseidon
// round-constant coefficients, o1js vs Lean, as an ordered vector; the harness owns the walk, the
// first-divergence citation, the exit code, and the RED-PATH self-test (`--self-test`). The CompleteAdd
// typ/coeff-freeness and the wires-DIVERGENCE note stay here as `extra` provenance.
//
// Two INDEPENDENT sources:
//   - o1js 2.15.0 `Provable.constraintSystem(f).gates` (OCaml/wasm bindings) — the byte target.
//   - Lean `Dregg2/Circuit/Emit/PastaPoseidon.lean` `def rcsN`, whose 55x3 = 165 round constants are
//     dumped from the pinned `proof-systems` crate. We read `rcsN` straight from the Lean source, so
//     the diff is o1js-vs-Lean, not o1js-vs-o1js.
//
// Run:  node scripts/custom-gate-diff.mjs [--self-test]
import { Field, Poseidon, Group, Provable } from 'o1js';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { runOracle } from './diff-oracle.mjs';

const LEAN_PP = new URL('../../../metatheory/Dregg2/Circuit/Emit/PastaPoseidon.lean', import.meta.url);

// ---- extract the 55x3 = 165 round constants from the Lean `def rcsN` block ----
function leanRcsN() {
  const src = readFileSync(LEAN_PP, 'utf8');
  const start = src.indexOf('def rcsN');
  if (start < 0) throw new Error('rcsN not found in PastaPoseidon.lean');
  const end = src.indexOf('#guard', start); // the block ends at the first #guard after the def
  const block = src.slice(start, end);
  const nums = (block.match(/\d{40,}/g) || []).map((s) => BigInt(s)); // 40+ digit literals, in order
  return nums; // 165, round-major then lane
}

async function poseidonGates() {
  const cs = await Provable.constraintSystem(() => {
    const a = Provable.witness(Field, () => Field(1));
    const b = Provable.witness(Field, () => Field(2));
    Poseidon.hash([a, b]).seal();
  });
  return cs.gates.filter((g) => g.type === 'Poseidon');
}

// REFERENCE (a): o1js poseidon coeffs, flattened round-major (row j = flat 15j..15j+14).
export async function reference() {
  const ps = await poseidonGates();
  const v = [];
  for (let j = 0; j < ps.length; j++)
    for (let k = 0; k < ps[j].coeffs.length; k++)
      v.push({ name: `poseidon.coeff[${15 * j + k}]`, value: BigInt(ps[j].coeffs[k]) });
  return v;
}

// CANDIDATE (b): Lean `rcsN`, one entry per flat index (names line up with the reference).
export function candidate() {
  return leanRcsN().map((n, idx) => ({ name: `poseidon.coeff[${idx}]`, value: n }));
}

// EXTRA provenance: rcsN length, CompleteAdd typ+coeff-freeness, and the wires-DIVERGENCE note.
export async function extra() {
  const rcs = leanRcsN();
  if (rcs.length !== 165) throw new Error(`Lean rcsN length ${rcs.length} != 165 (expect 55*3)`);
  console.log('  ok   Lean rcsN length 165 (55 rounds x 3 lanes)');

  const caCS = await Provable.constraintSystem(() => {
    const g1 = Provable.witness(Group, () => Group.generator);
    const g2 = Provable.witness(Group, () => Group.generator.add(Group.generator));
    g1.add(g2).x.seal();
  });
  const ca = caCS.gates.filter((g) => g.type === 'CompleteAdd');
  if (ca.length !== 1) throw new Error(`expected exactly 1 CompleteAdd gate, saw ${ca.length}`);
  if (ca[0].coeffs.length !== 0)
    throw new Error(`CompleteAdd coeffs ${JSON.stringify(ca[0].coeffs)} != [] (Lean mkCompleteAdd.coeffs=[])`);
  console.log("  ok   CompleteAdd: exactly one row, coeffs=[] (Lean KGateType.completeAdd ordinal 3, mkCompleteAdd.coeffs=[])");
  console.log(
    `  note wires DIVERGE by design: o1js emits ${ca[0].wires.length} placement cells {row,col}; ` +
      'Lean KRow.wires holds pre-placement variable indices (the placed-wire diff is pickles-placement-oracle).'
  );
}

export const shape = 'gates';
export const label = 'R1 custom-gate poseidon coeffs (o1js 2.15.0 vs Lean rcsN)';

const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
if (isMain) await runOracle({ shape, label, reference, candidate, extra });
