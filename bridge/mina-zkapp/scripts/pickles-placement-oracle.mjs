// R1 PLACEMENT byte-DIFF — o1js's live {row,col} wiring vs the Lean placement pass's goldens.
//
// Two INDEPENDENT sources:
//   - o1js 2.15.0 `Provable.constraintSystem(f).gates[i].wires` (OCaml/wasm bindings) — byte target.
//   - Lean `Dregg2/Circuit/Emit/KimchiPlacement.lean` `caseA_o1js` / `caseB_o1js` goldens, which the
//     Lean `place` pass is proven equal to (`caseA_wires_match_o1js`, `caseB_wires_match_o1js`).
//     We read those goldens straight from the Lean source, so the diff is o1js-live-vs-Lean, and the
//     Lean theorem closes place = golden = live-o1js.
//
// This pins the exact Snarky sigma placement (`plonk_constraint_system.ml`): a public-input-free
// circuit, cols 0..6 wired, each equivalence class SORTED + ROTATED-LEFT, cell -> next-in-cycle,
// unwired cells self-wired. Case B carries the smallest cross-row COPY (a 3-cell class over 2 rows).
//
// green-or-bust: exits non-zero if ANY cell diverges. NEW file (does not clobber
// custom-gate-oracle.mjs / custom-gate-diff.mjs).
//
// Run: node scripts/pickles-placement-oracle.mjs
import { Field, Provable } from 'o1js';
import { readFileSync } from 'node:fs';

const LEAN = new URL(
  '../../../metatheory/Dregg2/Circuit/Emit/KimchiPlacement.lean',
  import.meta.url
);

let fails = 0;
const ok = (m) => console.log('  ok  ' + m);
const bad = (m) => { fails++; console.log('  RED ' + m); };

// ---- extract a `def NAME : ... := [ [⟨r,c⟩,...], ... ]` golden from the Lean source ----
// returns an array of gates, each an array of [row,col] pairs (7 per gate).
function leanGolden(name, gatesExpected) {
  const src = readFileSync(LEAN, 'utf8');
  const start = src.indexOf(`def ${name}`);
  if (start < 0) throw new Error(`${name} not found in KimchiPlacement.lean`);
  // block ends at the next `theorem`/`def `/`/--` after the `:=`
  const afterEq = src.indexOf(':=', start);
  const rest = src.slice(afterEq + 2);
  const endRel = Math.min(
    ...['\ntheorem', '\ndef ', '\n/--', '\n/-!'].map((m) => {
      const i = rest.indexOf(m);
      return i < 0 ? rest.length : i;
    })
  );
  const block = rest.slice(0, endRel);
  const pairs = [...block.matchAll(/⟨\s*(\d+)\s*,\s*(\d+)\s*⟩/g)].map((m) => [
    Number(m[1]),
    Number(m[2]),
  ]);
  if (pairs.length !== gatesExpected * 7)
    throw new Error(`${name}: parsed ${pairs.length} cells, expected ${gatesExpected * 7}`);
  const gates = [];
  for (let g = 0; g < gatesExpected; g++) gates.push(pairs.slice(g * 7, g * 7 + 7));
  return gates;
}

async function liveWires(f) {
  const cs = await Provable.constraintSystem(f);
  return { rows: cs.rows, pub: cs.publicInputSize, digest: cs.digest, gates: cs.gates };
}

// diff live o1js wires against the Lean golden, cell by cell.
function diff(label, live, golden) {
  console.log(`\n[${label}] o1js rows=${live.rows} pub=${live.pub} digest=${live.digest}`);
  if (live.gates.length !== golden.length) {
    bad(`gate count ${live.gates.length} != Lean golden ${golden.length}`);
    return;
  }
  let cells = 0;
  for (let g = 0; g < golden.length; g++) {
    const lw = live.gates[g].wires;
    if (lw.length !== 7) { bad(`gate ${g}: o1js emitted ${lw.length} wires, expected 7`); continue; }
    for (let c = 0; c < 7; c++) {
      const [lr, lc] = [lw[c].row, lw[c].col];
      const [gr, gc] = golden[g][c];
      if (lr === gr && lc === gc) cells++;
      else bad(`gate ${g} col ${c}: o1js (${lr},${lc}) != Lean (${gr},${gc})`);
    }
  }
  if (cells === golden.length * 7)
    ok(`ALL ${cells} placement cells BYTE-EXACT: o1js == Lean place goldens`);
}

console.log('=== R1 placement byte-diff: o1js 2.15.0  vs  Lean KimchiPlacement goldens ===');

// Case A: x + y === 8  (o1js example constraint-system.ts) — base placement, one within-row copy.
const A = await liveWires(() => {
  const x = Provable.witness(Field, () => Field(3));
  const y = Provable.witness(Field, () => Field(5));
  x.add(y).assertEquals(Field(8));
});
diff('A: x + y === 8', A, leanGolden('caseA_o1js', 1));

// Case B: one variable copied across TWO rows — the smallest falsifiable cross-row placement.
const B = await liveWires(() => {
  const x = Provable.witness(Field, () => Field(7));
  x.mul(x).assertEquals(Field(49)); // x in two same-row cells
  x.add(Field(1)).assertEquals(Field(8)); // x again, a different row -> 3-cell cross-row class
});
diff('B: x used in two rows (copy)', B, leanGolden('caseB_o1js', 2));

console.log('\n=== ' + (fails ? `RED — ${fails} cell(s) diverged` : 'GREEN — all placement cells byte-exact') + ' ===');
process.exit(fails ? 1 : 0);
