// R1 custom-gate BYTE-DIFF — o1js's emitted custom-gate rows vs the Lean emitter's.
//
// Two INDEPENDENT sources:
//   - o1js 2.15.0 `Provable.constraintSystem(f).gates` (OCaml/wasm bindings) — the byte target.
//   - Lean `Dregg2/Circuit/Emit/KimchiCustomGates.lean` emitter, whose poseidon coefficients are
//     `PastaPoseidon.rcsN` (dumped from the pinned `proof-systems` crate). We read `rcsN` straight
//     from the Lean source here so the diff is o1js-vs-Lean, not o1js-vs-o1js.
//
// Reports, field by field: typ, coeffs (byte-exact), wires (structural divergence).
import { Field, Poseidon, Group, Provable } from 'o1js';
import { readFileSync } from 'node:fs';

const LEAN_PP = new URL(
  '../../../metatheory/Dregg2/Circuit/Emit/PastaPoseidon.lean',
  import.meta.url
);

let fails = 0;
const ok = (m) => console.log('  ok  ' + m);
const bad = (m) => {
  fails++;
  console.log('  RED ' + m);
};

// ---- extract the 55x3 = 165 round constants from the Lean `def rcsN` block ----
function leanRcsN() {
  const src = readFileSync(LEAN_PP, 'utf8');
  const start = src.indexOf('def rcsN');
  if (start < 0) throw new Error('rcsN not found in PastaPoseidon.lean');
  // the block ends at the first `#guard` after the def
  const end = src.indexOf('#guard', start);
  const block = src.slice(start, end);
  // every 40+ digit integer literal in the block, in order
  const nums = block.match(/\d{40,}/g).map((s) => BigInt(s));
  return nums; // 165 of them, round-major then lane
}

async function gatesOf(f) {
  const cs = await Provable.constraintSystem(f);
  return cs.gates;
}

console.log('=== R1 custom-gate byte-diff: o1js 2.15.0  vs  Lean KimchiCustomGates ===\n');

const rcs = leanRcsN();
console.log(`[lean] rcsN carries ${rcs.length} round constants (expect 165 = 55*3)`);
if (rcs.length !== 165) bad(`rcsN length ${rcs.length} != 165`);
else ok('rcsN length 165');

// ---------- (1) complete_add ----------
console.log('\n[1] complete_add  (Group g1 + g2)');
const caGates = await gatesOf(() => {
  const g1 = Provable.witness(Group, () => Group.generator);
  const g2 = Provable.witness(Group, () => Group.generator.add(Group.generator));
  g1.add(g2).x.seal();
});
const ca = caGates.filter((g) => g.type === 'CompleteAdd');
if (ca.length !== 1) bad(`expected exactly 1 CompleteAdd gate, saw ${ca.length}`);
else ok('exactly one CompleteAdd row emitted');
if (ca.length) {
  const g = ca[0];
  // typ
  if (g.type === 'CompleteAdd') ok("typ = 'CompleteAdd'  (Lean KGateType.completeAdd, ordinal 3)");
  else bad(`typ = ${g.type}`);
  // coeffs — Lean emits []
  if (g.coeffs.length === 0) ok('coeffs = []   (Lean mkCompleteAdd.coeffs = [] — MATCH)');
  else bad(`coeffs = ${JSON.stringify(g.coeffs)}  (Lean emits [])`);
  // wires — DIVERGENCE
  console.log(
    `  DIVERGE wires: o1js emits ${g.wires.length} placement cells {row,col} ` +
      `(PERMUTS=7 copy targets); Lean KRow.wires holds 11 VARIABLE INDICES pre-placement.`
  );
  console.log('          o1js wires =', JSON.stringify(g.wires));
}

// ---------- (2) poseidon ----------
console.log('\n[2] poseidon  (Poseidon.hash([1,2]))');
const psGates = await gatesOf(() => {
  const a = Provable.witness(Field, () => Field(1));
  const b = Provable.witness(Field, () => Field(2));
  Poseidon.hash([a, b]).seal();
});
const ps = psGates.filter((g) => g.type === 'Poseidon');
console.log(`  o1js emitted ${ps.length} Poseidon rows (expect 11 = 55 rounds / 5 per row)`);
if (ps.length !== 11) bad(`Poseidon row count ${ps.length} != 11`);
else ok('11 Poseidon rows');

// typ + coeff length per row
let typOk = ps.every((g) => g.type === 'Poseidon');
typOk ? ok("every row typ = 'Poseidon'  (Lean KGateType.poseidon, ordinal 2)") : bad('a Poseidon row had wrong typ');
let lenOk = ps.every((g) => g.coeffs.length === 15);
lenOk ? ok('every row carries 15 coeffs') : bad('a Poseidon row had != 15 coeffs');

// BYTE-EXACT coeff diff, all 165, o1js vs Lean rcsN (round-major, lane-minor: row j = rcsN[5j..5j+4])
let firstDiff = null;
let matched = 0;
for (let j = 0; j < ps.length; j++) {
  for (let k = 0; k < ps[j].coeffs.length; k++) {
    const idx = 15 * j + k; // flat index into the 165 round constants
    const o1 = BigInt(ps[j].coeffs[k]);
    const le = rcs[idx];
    if (o1 === le) matched++;
    else if (!firstDiff) firstDiff = { row: j, col: k, idx, o1: o1.toString(), lean: le.toString() };
  }
}
if (firstDiff)
  bad(
    `poseidon coeff DIVERGES at row ${firstDiff.row} coeff ${firstDiff.col} ` +
      `(flat #${firstDiff.idx}): o1js=${firstDiff.o1}  lean=${firstDiff.lean}`
  );
else ok(`ALL ${matched} poseidon coefficients BYTE-EXACT: o1js == Lean rcsN[5j..5j+4] (round-major)`);

// wires divergence, same structural note
console.log(
  `  DIVERGE wires: o1js emits ${ps[0]?.wires.length ?? '?'} placement cells {row,col} per row; ` +
    'Lean KRow.wires holds variable indices pre-placement (KimchiPartition remainder).'
);

console.log('\n=== ' + (fails ? `RED — ${fails} check(s) failed` : 'GREEN — all byte-diffs matched') + ' ===');
process.exit(fails ? 1 : 0);
