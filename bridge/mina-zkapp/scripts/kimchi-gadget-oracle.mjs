// KIMCHI GADGET byte-DIFF — o1js's live Generic-gate coefficients vs the Lean gadget rail's.
//
// WHY THIS EXISTS. `Dregg2/Circuit/Emit/KimchiGadgets.lean` is the tree's first `Boolean`/`select`/
// `assertEq`/one-hot library on the kimchi rail. Before it, `Field.if_` appeared 25 times in
// `metatheory/` and every one was a COMMENT; the mux was open-coded three times and booleanity had
// no name at all. A gadget library is only worth anything if what it emits is what Snarky emits, so
// every coefficient vector below is diffed against o1js 2.15.0's own `Provable.constraintSystem`.
//
// Two INDEPENDENT sources:
//   - o1js 2.15.0 `Provable.constraintSystem(f).gates[i].coeffs` (OCaml/wasm bindings) — byte target.
//   - the Lean `def cBool/cSub/cMul/cAdd/cEq/cConst` literals, READ OUT OF THE LEAN SOURCE, so the
//     diff is o1js-live-vs-Lean-source and not a transcription this file made up.
//
// ⚑ WHAT IT PINS, and the one place we are DELIBERATELY STRICTER.
//   * `Bool` witness check   → ONE half, `[-1,0,0,1,0]`  (`b·b − b`). This is `cBool`.
//   * `Provable.if(b,x,y)`   → THREE halves: sub, mul, add. This is `selectHalves`.
//   * `x.assertEquals(y)` on two BARE variables → ZERO rows. That is Snarky's union-find, i.e.
//     `KimchiPlacement`'s merge seam, NOT a gate — which is why `assertEqHalf` is the other case.
//   * `x.assertEquals(Field k)` → ONE half `[1,0,0,0,-k]`. This is `cConst`.
//   * `x.add(y).assertEquals(z)` → ONE half `[1,1,-1,0,0]`. This is `cAdd`.
//   * ⚠ `Provable.switch` over a 3-way mask emits 3 booleanity + 3 mul + 2 add halves and **NO
//     `Σ mask = 1` gate**: its exclusivity check is `Provable.asProver(checkMask)`
//     (`provable.js:353-370`), i.e. OUTSIDE the circuit. A prover choosing mask `[1,1,0]` satisfies
//     every gate o1js emits. `KimchiGadgets.oneHotHalves` emits the sum gate, so its row count is
//     HIGHER than o1js's by design and is asserted here as a DELIBERATE divergence, not diffed away.
//
// Run: node scripts/kimchi-gadget-oracle.mjs [--self-test]
import { Field, Bool, Provable } from 'o1js';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { runOracle } from './diff-oracle.mjs';

const LEAN = new URL('../../../metatheory/Dregg2/Circuit/Emit/KimchiGadgets.lean', import.meta.url);
const PROVABLE_JS = new URL('../node_modules/o1js/dist/node/lib/provable/provable.js', import.meta.url);

// Pasta Fp — o1js reports coefficients as unsigned field elements; fold to signed for comparison.
const P = 28948022309329048855892746252171976963363056481941560715954676764349967630337n;
const signed = (c) => {
  const v = BigInt(c);
  return v > P / 2n ? v - P : v;
};

// ---- extract a `def NAME : List Int := [a, b, c, d, e]` literal out of the Lean source.
function leanCoeffs(name) {
  const src = readFileSync(LEAN, 'utf8');
  const m = src.match(new RegExp(`def\\s+${name}\\s*:\\s*List Int\\s*:=\\s*\\[([^\\]]*)\\]`));
  if (!m) throw new Error(`${name} not found as a List Int literal in KimchiGadgets.lean`);
  const xs = m[1].split(',').map((s) => BigInt(s.trim()));
  if (xs.length !== 5) throw new Error(`${name}: parsed ${xs.length} coefficients, expected 5`);
  return xs;
}

// `cConst k = [1, 0, 0, 0, -k]` is a FUNCTION in Lean; read its body and instantiate at k.
function leanConst(k) {
  const src = readFileSync(LEAN, 'utf8');
  if (!/def\s+cConst\s*\(k\s*:\s*Int\)\s*:\s*List Int\s*:=\s*\[1,\s*0,\s*0,\s*0,\s*-k\]/.test(src))
    throw new Error('cConst is not the expected `[1, 0, 0, 0, -k]` in KimchiGadgets.lean');
  return [1n, 0n, 0n, 0n, -BigInt(k)];
}

// The five gadget cases. Each names the halves it expects, in emission order.
const K = 7; // the constant `assertEquals` compares against

const CASES = [
  {
    key: 'bool',
    // A `Bool` witness: o1js emits its booleanity check and nothing else.
    f: () => {
      Provable.witness(Bool, () => Bool(true));
    },
    lean: () => [{ name: 'bool.half[0]', value: leanCoeffs('cBool').join('|') }],
  },
  {
    key: 'mux',
    // `Provable.if` on a CONSTANT-free selector: sub, mul, add — plus the Bool's own booleanity.
    // The witness Bool is created first so its booleanity lands in a known half; we read only the
    // three mux halves by name below.
    f: () => {
      const b = Provable.witness(Bool, () => Bool(true));
      const x = Provable.witness(Field, () => Field(11));
      const y = Provable.witness(Field, () => Field(22));
      Provable.if(b, x, y).assertEquals(Field(11));
    },
    lean: () => [
      { name: 'mux.half[sub]', value: leanCoeffs('cSub').join('|') },
      { name: 'mux.half[mul]', value: leanCoeffs('cMul').join('|') },
      { name: 'mux.half[add]', value: leanCoeffs('cAdd').join('|') },
    ],
  },
  {
    key: 'assertConst',
    f: () => {
      const x = Provable.witness(Field, () => Field(K));
      x.assertEquals(Field(K));
    },
    lean: () => [{ name: 'assertConst.half[0]', value: leanConst(K).join('|') }],
  },
  {
    key: 'assertSum',
    f: () => {
      const x = Provable.witness(Field, () => Field(3));
      const y = Provable.witness(Field, () => Field(4));
      const z = Provable.witness(Field, () => Field(7));
      x.add(y).assertEquals(z);
    },
    lean: () => [{ name: 'assertSum.half[0]', value: leanCoeffs('cAdd').join('|') }],
  },
];

// Split a gate's 10 coefficients into its two Generic halves, dropping all-zero (unused) halves.
function halvesOf(gate) {
  const c = gate.coeffs.map(signed);
  const out = [];
  for (const h of [c.slice(0, 5), c.slice(5, 10)]) {
    if (h.length === 5 && h.some((v) => v !== 0n)) out.push(h.join('|'));
  }
  return out;
}

// REFERENCE (a): o1js's live coefficient halves, in emission order, per case.
export async function reference() {
  const out = [];
  for (const { key, f } of CASES) {
    const cs = await Provable.constraintSystem(f);
    const halves = cs.gates.flatMap(halvesOf);
    console.log(`  [${key}] o1js rows=${cs.rows} halves=${halves.length}`);
    if (key === 'bool') {
      out.push({ name: 'bool.half[0]', value: halves[0] });
    } else if (key === 'mux') {
      // halves: [sub, booleanity, add, mul, constAssert] in o1js's own packing order — pick the
      // three mux halves by their coefficient shape rather than by position, so a repacking upstream
      // does not silently re-point the diff.
      const sub = halves.find((h) => h === '1|-1|-1|0|0');
      const mul = halves.find((h) => h === '0|0|1|-1|0' || h === '0|0|-1|1|0');
      const add = halves.find((h) => h === '1|1|-1|0|0');
      // o1js writes the mul half as `w₂ − w₀·w₁`; dregg writes `w₀·w₁ − w₂`. Same constraint, the
      // negation of the same polynomial — normalize the SIGN so the diff compares the gate and not
      // an arbitrary orientation. This is the one normalization in this file and it is stated.
      const mulNorm = mul === '0|0|1|-1|0' ? '0|0|-1|1|0' : mul;
      out.push({ name: 'mux.half[sub]', value: sub });
      out.push({ name: 'mux.half[mul]', value: mulNorm });
      out.push({ name: 'mux.half[add]', value: add });
    } else {
      out.push({ name: `${key}.half[0]`, value: halves[0] });
    }
  }
  return out;
}

// CANDIDATE (b): the Lean gadget rail's own coefficient literals, same order.
export function candidate() {
  return CASES.flatMap(({ lean }) => lean());
}

// ── (c) shape-specific provenance the vector diff cannot carry ────────────────────────────────────
export async function extra() {
  const fails = [];

  // ⚑ `assertEquals` on two BARE VARIABLES is ZERO ROWS. That is the merge seam, not a gate.
  const eqCs = await Provable.constraintSystem(() => {
    const x = Provable.witness(Field, () => Field(7));
    const y = Provable.witness(Field, () => Field(7));
    x.assertEquals(y);
  });
  console.log(`  [assertEqVarVar] o1js rows=${eqCs.rows} (expected 0 — Snarky union-find)`);
  if (eqCs.rows !== 0) fails.push(`assertEquals(var,var) emitted ${eqCs.rows} rows, expected 0`);

  // ⚑ AND `Provable.switch` emits NO exclusivity gate. Measured two ways: the row/half census, and
  // the code path in o1js's own bundle.
  const swCs = await Provable.constraintSystem(() => {
    const xs = [11, 22, 33].map((v) => Provable.witness(Field, () => Field(v)));
    const m = [0, 1, 2].map((i) => Provable.witness(Bool, () => Bool(i === 1)));
    Provable.switch(m, Field, xs).assertEquals(xs[1]);
  });
  const swHalves = swCs.gates.flatMap(halvesOf);
  const nBool = swHalves.filter((h) => h === '-1|0|0|1|0').length;
  const nMul = swHalves.filter((h) => h === '0|0|1|-1|0' || h === '0|0|-1|1|0').length;
  const nAdd = swHalves.filter((h) => h === '1|1|-1|0|0').length;
  const nSumPin = swHalves.filter((h) => h === '1|0|0|0|-1').length;
  console.log(
    `  [switch3] o1js rows=${swCs.rows} booleanity=${nBool} mul=${nMul} add=${nAdd} sumPin=${nSumPin}`
  );
  if (nBool !== 3) fails.push(`Provable.switch: ${nBool} booleanity halves, expected 3`);
  if (nSumPin !== 0)
    fails.push(`Provable.switch emitted a Σ=1 pin (${nSumPin}); the stated divergence is stale`);

  const src = readFileSync(PROVABLE_JS, 'utf8');
  const asProver = /Provable\.asProver\(checkMask\)/.test(src);
  console.log(`  [switch3] exclusivity check is Provable.asProver: ${asProver}`);
  if (!asProver)
    fails.push('provable.js no longer routes checkMask through asProver; re-read the divergence');

  // ⚑ AND OURS EMITS IT. The Lean rail's one-hot appends a `constHalf … 1`; grep the source so the
  // "deliberately stricter" claim is checked and not asserted.
  const leanSrc = readFileSync(LEAN, 'utf8');
  if (!/def oneHotHalves[\s\S]{0,400}constHalf \(lastOut s0 steps\) 1/.test(leanSrc))
    fails.push('KimchiGadgets.oneHotHalves no longer emits the Σ=1 pin');
  console.log('  [switch3] Lean oneHotHalves emits the Σ=1 pin: true');

  return fails;
}

export const shape = 'gates';
export const label =
  'kimchi gadget coefficients (o1js 2.15.0 live Generic coeffs vs Lean KimchiGadgets literals)';

const isMain = process.argv[1] && fileURLToPath(import.meta.url) === resolve(process.argv[1]);
if (isMain) await runOracle({ shape, label, reference, candidate, extra });
