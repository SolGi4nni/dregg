// AUTHORITATIVE ORACLE for R1's internal_vars/rows_rev residual.
//
// Produces the REAL rows_rev / internal_vars for R1's fixed toy circuits by reaching o1js's
// live OCaml constraint system `cs` (the SAME object o1js's `dump_extra_circuit_data`
// serialises into `_rows_rev.bin` / `_internal_vars.bin`). We monkey-patch
// `Snarky.constraintSystem.toJson` (called inside `Provable.constraintSystem`) to capture `cs`,
// then decode `cs[3]` (rows_rev = `V.t option array list`) and `cs[2]` (internal_vars =
// `Internal_var.Table.t`, a Core Hashtbl). o1js 2.15.0.
//
// `cs` field order (plonk_constraint_system.ml `type t`, tag at [0]):
//   [1]=equivalence_classes [2]=internal_vars [3]=rows_rev [4]=gates ...
// V.t js_of_ocaml repr: External of int = [0,i]; Internal of int = [1,i].
//
// Run: node oracle/extract-reference.mjs <abs path to o1js dist/node>
// (defaults to the breadstuffs bridge/mina-zkapp install)
import { writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';

const O1JS_DIST =
  process.argv[2] ||
  '/Users/ember/dev/breadstuffs/bridge/mina-zkapp/node_modules/o1js/dist/node';
const { Field, Provable } = await import(pathToFileURL(O1JS_DIST + '/index.js').href);
const b = await import(pathToFileURL(O1JS_DIST + '/bindings.js').href);
await b.initializeBindings();
const Snarky = b.Snarky; // access AFTER init (dynamic-import destructure is not a live binding)

let captured = null;
const realToJson = Snarky.constraintSystem.toJson;
Snarky.constraintSystem.toJson = function (cs) { captured = cs; return realToJson(cs); };
async function grab(f) { captured = null; const res = await Provable.constraintSystem(f); return { cs: captured, res }; }

const decV = (v) => (v[0] === 0 ? { kind: 'External', i: v[1] } : { kind: 'Internal', i: v[1] });
const decOpt = (o, f) => (o === 0 ? null : f(o[1]));
const decArr = (a) => { const o = []; for (let i = 1; i < a.length; i++) o.push(a[i]); return o; };
const decList = (l) => { const o = []; let c = l; while (c !== 0) { o.push(c[1]); c = c[2]; } return o; };
// rows_rev is stored REVERSED (most-recent row first) — this is the ON-DISK order the .bin holds.
const rowsRevOnDisk = (rr) => decList(rr).map((row) => decArr(row).map((cell) => decOpt(cell, decV)));

// Core Avltree walk (Empty=0; Leaf=[0,key,data]; Node=[1,left,key,data,right,height]).
function walkAvl(n, out) {
  if (n === 0 || !Array.isArray(n)) return;
  if (n[0] === 0 && n.length === 3) out.push([n[1], n[2]]);
  else if (n[0] === 1 && n.length >= 5) { walkAvl(n[1], out); out.push([n[2], n[3]]); walkAvl(n[4], out); }
}
function internalVarsCount(ht) {
  let count = 0;
  for (let i = 1; i < ht.length; i++) {
    const f = ht[i];
    if (Array.isArray(f) && f[0] === 0 && f.slice(1).every((x) => x === null || x === 0 || Array.isArray(x))) {
      const acc = [];
      for (let b = 1; b < f.length; b++) if (f[b] && f[b] !== 0) walkAvl(f[b], acc);
      count = Math.max(count, acc.length);
    }
  }
  return count;
}

const cases = {
  caseA: () => { const x = Provable.witness(Field, () => Field(3)); const y = Provable.witness(Field, () => Field(5)); x.add(y).assertEquals(Field(8)); },
  caseB: () => { const x = Provable.witness(Field, () => Field(7)); x.mul(x).assertEquals(Field(49)); x.add(Field(1)).assertEquals(Field(8)); },
};
for (const [name, f] of Object.entries(cases)) {
  const g = await grab(f);
  const ref = {
    circuit: name,
    o1js_version: '2.15.0',
    source: 'live o1js OCaml cs[3]/cs[2] (== dump_extra_circuit_data serialises these)',
    rows: g.res.rows,
    publicInputSize: g.res.publicInputSize,
    wires: g.res.gates.map((gt) => gt.wires.map((w) => [w.row, w.col])),
    rows_rev_on_disk: rowsRevOnDisk(g.cs[3]), // reversed row order, as the .bin stores it
    internal_vars_count: internalVarsCount(g.cs[2]),
  };
  const out = new URL(`../reference/${name}.json`, import.meta.url);
  writeFileSync(out, JSON.stringify(ref, null, 2));
  console.log(`${name}: rows=${ref.rows} internal_vars=${ref.internal_vars_count} rows_rev_on_disk=${JSON.stringify(ref.rows_rev_on_disk)}`);
}
