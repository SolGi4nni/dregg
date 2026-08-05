// READ-ONLY o1js ORACLE — what does `assertEquals` between two ALREADY-ALLOCATED values COST?
//
// This is the measurement `Dregg2.Circuit.Emit.KimchiAssertEqual` is built to match. Snarky's
// `assert_equal` unions the two variables' equivalence classes (`plonk_constraint_system.ml:764`)
// and emits NO gate; the equality is carried by the copy permutation. If a Lean `assertEqual` cost
// a `Generic` row, every circuit built on it would diverge from o1js's gate count — so the claim is
// measured here rather than relayed.
//
//   node bridge/mina-zkapp/scripts/assert-equal-row-cost-oracle.mjs
//
// MEASURED 2026-08-05, o1js 2.15.0: delta = 0 rows in both shapes, gate sequence unchanged.
import { Provable, Field, Poseidon } from 'o1js';

async function cs(name, f) {
  const r = await Provable.constraintSystem(f);
  const typs = r.gates.map((g) => g.type);
  console.log(`${name.padEnd(36)} rows=${String(r.rows).padStart(3)}  gates=[${typs.join(',')}]`);
  return r;
}

// (a) two plain witnesses, each constrained, with and without the equality between them
const A = await cs('two witnesses, NO assertEquals', () => {
  const a = Provable.witness(Field, () => Field(3));
  const b = Provable.witness(Field, () => Field(3));
  a.mul(a).assertEquals(Field(9));
  b.mul(b).assertEquals(Field(9));
});
const B = await cs('two witnesses, assertEquals', () => {
  const a = Provable.witness(Field, () => Field(3));
  const b = Provable.witness(Field, () => Field(3));
  a.mul(a).assertEquals(Field(9));
  b.mul(b).assertEquals(Field(9));
  a.assertEquals(b);
});

// (b) THE PREIMAGE SHAPE: `Poseidon.hash([x])` bound to a separately-allocated claim.
const C = await cs('Poseidon.hash([x]), NO assertEquals', () => {
  const x = Provable.witness(Field, () => Field(20260805));
  const h = Poseidon.hash([x]);
  const c = Provable.witness(Field, () => Field(1));
  c.mul(c).assertEquals(Field(1));
  h.add(0);
});
const D = await cs('Poseidon.hash([x]), assertEquals(c)', () => {
  const x = Provable.witness(Field, () => Field(20260805));
  const h = Poseidon.hash([x]);
  const c = Provable.witness(Field, () => Field(1));
  c.mul(c).assertEquals(Field(1));
  h.assertEquals(c);
});

console.log();
console.log(`delta (two witnesses)  : ${B.rows - A.rows}`);
console.log(`delta (poseidon shape) : ${D.rows - C.rows}`);
const bad = B.rows - A.rows !== 0 || D.rows - C.rows !== 0;
console.log(bad ? 'RED: assertEquals COST a row here' : 'ZERO ROWS: the copy permutation carries it');
process.exit(bad ? 1 : 0);
