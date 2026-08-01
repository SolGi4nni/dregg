// R1 PLACEMENT byte-DIFF — o1js's live {row,col} wiring vs the Lean placement pass's goldens.
//
// MIGRATED to the shared `diff-oracle.mjs` harness (shape `gates`): both cases (A + B) are flattened
// into ONE ordered vector of placement cells ({row,col}), and the harness owns the cell-by-cell walk,
// the first-divergence citation, the exit code, and the RED-PATH self-test (`--self-test`).
//
// Two INDEPENDENT sources:
//   - o1js 2.15.0 `Provable.constraintSystem(f).gates[i].wires` (OCaml/wasm bindings) — byte target.
//   - Lean `Dregg2/Circuit/Emit/KimchiPlacement.lean` `caseA_o1js` / `caseB_o1js` goldens, which the
//     Lean `place` pass is proven equal to (`caseA_wires_match_o1js`, `caseB_wires_match_o1js`). We read
//     those goldens straight from the Lean source, so the diff is o1js-live-vs-Lean and the Lean theorem
//     closes place = golden = live-o1js.
//
// This pins the exact Snarky sigma placement: a public-input-free circuit, cols 0..6 wired, each
// equivalence class SORTED + ROTATED-LEFT, cell -> next-in-cycle, unwired cells self-wired. Case B
// carries the smallest cross-row COPY (a 3-cell class over 2 rows).
//
// Run: node scripts/pickles-placement-oracle.mjs [--self-test]
import { Field, Provable } from 'o1js';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { runOracle } from './diff-oracle.mjs';

const LEAN = new URL('../../../metatheory/Dregg2/Circuit/Emit/KimchiPlacement.lean', import.meta.url);

// ---- extract a `def NAME : ... := [ [⟨r,c⟩,...], ... ]` golden: array of gates, each 7 [row,col] cells.
function leanGolden(name, gatesExpected) {
  const src = readFileSync(LEAN, 'utf8');
  const start = src.indexOf(`def ${name}`);
  if (start < 0) throw new Error(`${name} not found in KimchiPlacement.lean`);
  const afterEq = src.indexOf(':=', start);
  const rest = src.slice(afterEq + 2);
  const endRel = Math.min(
    ...['\ntheorem', '\ndef ', '\n/--', '\n/-!'].map((m) => {
      const i = rest.indexOf(m);
      return i < 0 ? rest.length : i;
    })
  );
  const block = rest.slice(0, endRel);
  const pairs = [...block.matchAll(/⟨\s*(\d+)\s*,\s*(\d+)\s*⟩/g)].map((m) => [Number(m[1]), Number(m[2])]);
  if (pairs.length !== gatesExpected * 7)
    throw new Error(`${name}: parsed ${pairs.length} cells, expected ${gatesExpected * 7}`);
  const gates = [];
  for (let g = 0; g < gatesExpected; g++) gates.push(pairs.slice(g * 7, g * 7 + 7));
  return gates;
}

// The two falsifiable cases: A base placement (one within-row copy), B one variable copied across 2 rows.
const CASES = [
  {
    key: 'A', // x + y === 8
    f: () => {
      const x = Provable.witness(Field, () => Field(3));
      const y = Provable.witness(Field, () => Field(5));
      x.add(y).assertEquals(Field(8));
    },
    golden: () => leanGolden('caseA_o1js', 1),
  },
  {
    key: 'B', // x used in two rows -> 3-cell cross-row class
    f: () => {
      const x = Provable.witness(Field, () => Field(7));
      x.mul(x).assertEquals(Field(49));
      x.add(Field(1)).assertEquals(Field(8));
    },
    golden: () => leanGolden('caseB_o1js', 2),
  },
];

// REFERENCE (a): o1js live {row,col} wires, both cases flattened; prints rows/pub/digest per case.
export async function reference() {
  const out = [];
  for (const { key, f } of CASES) {
    const cs = await Provable.constraintSystem(f);
    console.log(`  [${key}] o1js rows=${cs.rows} pub=${cs.publicInputSize} digest=${cs.digest}`);
    cs.gates.forEach((g, gi) =>
      g.wires.forEach((w, c) => out.push({ name: `${key}.gate[${gi}].cell[${c}]`, value: { row: w.row, col: w.col } }))
    );
  }
  return out;
}

// CANDIDATE (b): the Lean place goldens, same flatten order (names line up with the reference).
export function candidate() {
  const out = [];
  for (const { key, golden } of CASES)
    golden().forEach((gate, gi) =>
      gate.forEach(([r, c], ci) => out.push({ name: `${key}.gate[${gi}].cell[${ci}]`, value: { row: r, col: c } }))
    );
  return out;
}

export const shape = 'gates';
export const label = 'R1 placement cells (o1js 2.15.0 live wires vs Lean KimchiPlacement goldens)';

const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
if (isMain) await runOracle({ shape, label, reference, candidate });
