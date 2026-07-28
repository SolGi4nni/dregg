// MEASURE: Kimchi rows for ONE Poseidon2-w16-BabyBear permutation, in o1js.
//
// `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.7 names this the first thing to
// build, because the whole ~2.2e7-row headline rests on a per-permutation figure
// it labels a DESIGN CLAIM (~2,000 rows), against a band whose pessimistic end
// (~8,400, from a measured gnark comparable) is 4x higher. This script emits the
// number, and re-derives the totals from it.
//
//   npm run poseidon2-rows
//
// It refuses to report a number for the wrong object: the circuit is checked,
// inside `Provable.runAndCheck`, against the bigint reference, which is itself
// checked against the two KAT vectors the Lean module pins bit-exact to the
// deployed Rust `default_babybear_poseidon2_16().permute(.)`.

import { Field, Provable, ZkProgram } from 'o1js';
import {
  P,
  permBigInt,
  probeSbox,
  probeMdsLight,
  probeExternalRound,
  probeInternalRound,
  probeReduceSboxOutput,
  provablePerm,
  provableCompress,
  KAT_RANGE16,
  KAT_ZERO16,
} from '../src/Poseidon2BabyBearW16.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);

// ---------------------------------------------------------------------------
// 1. The reference reproduces the deployed hash (Lean-pinned KAT).
// ---------------------------------------------------------------------------
console.log('=== Poseidon2-w16-BabyBear in o1js: row measurement ===\n');
console.log('[1] the bigint reference == the deployed Rust permutation (Lean KAT)');
{
  const got = permBigInt([...Array(16).keys()].map(BigInt));
  if (!eqv(got, KAT_RANGE16)) fail(`perm([0..15]) = ${got} != KAT ${KAT_RANGE16}`);
  ok('perm([0..15]) matches the deployed permutation');
  const z = permBigInt(Array(16).fill(0n));
  if (!eqv(z, KAT_ZERO16)) fail(`perm(0^16) = ${z} != KAT ${KAT_ZERO16}`);
  ok('perm(0^16) matches the deployed permutation');
  // Reject polarity: the KAT is discriminating.
  const t = permBigInt([1n, ...Array(15).fill(0n)]);
  if (eqv(t, KAT_ZERO16)) fail('a tampered input reproduced the zero-state KAT');
  ok('a tampered input does NOT reproduce the KAT');
}

// ---------------------------------------------------------------------------
// 2. The CIRCUIT computes the same function, checked with real witnesses.
// ---------------------------------------------------------------------------
console.log('\n[2] the o1js circuit computes the same permutation');
for (const input of [
  [...Array(16).keys()].map(BigInt),
  Array(16).fill(0n),
  [...Array(16).keys()].map((i) => (BigInt(i) * 123456789n) % P),
]) {
  const want = permBigInt(input);
  await Provable.runAndCheck(() => {
    const inp = input.map((x) => Provable.witness(Field, () => Field(x)));
    const out = provablePerm(inp);
    Provable.asProver(() => {
      const got = out.map((f) => f.toBigInt() % P);
      if (!eqv(got, want)) fail(`circuit output ${got} != reference ${want}`);
    });
  });
}
ok('3 inputs: circuit output == reference output (all constraints satisfied)');

// A wrong witness must make the constraint system unsatisfiable.
{
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const inp = [...Array(16).keys()].map((i) => Provable.witness(Field, () => Field(i)));
      const out = provablePerm(inp);
      out[0].assertEquals(Field(KAT_RANGE16[0] + 1n));
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the circuit accepted an output that is not the permutation');
  ok('the circuit REFUSES a wrong output (constraints bite)');
}

// ---------------------------------------------------------------------------
// 3. THE MEASUREMENT.
// ---------------------------------------------------------------------------
console.log('\n[3] getRows()');
async function rowsFor(nPerms: number): Promise<{ rows: number; summary: any }> {
  const cs = await Provable.constraintSystem(() => {
    let s = [...Array(16).keys()].map((i) => Provable.witness(Field, () => Field(i)));
    for (let k = 0; k < nPerms; k++) s = provablePerm(s);
    s.forEach((x) => x.seal());
  });
  return { rows: cs.rows, summary: cs.summary() };
}

const r1 = await rowsFor(1);
const r2 = await rowsFor(2);
const r3 = await rowsFor(3);
const marginal = (r3.rows - r1.rows) / 2;

console.log(`    1 permutation : ${r1.rows.toLocaleString()} rows`);
console.log(`    2 permutations: ${r2.rows.toLocaleString()} rows`);
console.log(`    3 permutations: ${r3.rows.toLocaleString()} rows`);
console.log(`    MARGINAL rows per permutation: ${marginal.toLocaleString()}`);
console.log(`    gate mix (1 perm): ${JSON.stringify(r1.summary)}`);

// The Merkle compression the MMCS actually calls is one permutation truncated.
const csCompress = await Provable.constraintSystem(() => {
  const a = [...Array(8).keys()].map((i) => Provable.witness(Field, () => Field(i)));
  const b = [...Array(8).keys()].map((i) => Provable.witness(Field, () => Field(i + 8)));
  provableCompress(a, b).forEach((x) => x.seal());
});
console.log(`    compress(l, r) (TruncatedPermutation<.,2,8,16>): ${csCompress.rows.toLocaleString()} rows`);

// Attribution: the same lines the design estimate used (§3.3-3.4), measured.
console.log('\n[3b] where the rows go (marginal, 2 copies minus 1)');
async function marginalRows(f: (n: number) => Promise<void>): Promise<number> {
  const a = await Provable.constraintSystem(() => f(1));
  const b = await Provable.constraintSystem(() => f(2));
  return (await b).rows - (await a).rows;
}
const w16 = () => [...Array(16).keys()].map((i) => Provable.witness(Field, () => Field(i)));
const parts: [string, number, string][] = [
  [
    'S-box x^7 (4 mults + 1 reduction)',
    await marginalRows(async (n) => {
      for (let i = 0; i < n; i++) probeSbox(Provable.witness(Field, () => Field(3))).seal();
    }),
    '141 per permutation',
  ],
  [
    '  of which: the mod-p reduction',
    await marginalRows(async (n) => {
      for (let i = 0; i < n; i++)
        probeReduceSboxOutput(Provable.witness(Field, () => Field(3))).seal();
    }),
    'one per S-box; unavoidable (x^7 doubles the width each step)',
  ],
  [
    'external linear layer (ADD-ONLY)',
    await marginalRows(async (n) => {
      for (let i = 0; i < n; i++) probeMdsLight(w16()).forEach((x) => x.seal());
    }),
    '9 per permutation (initial + 8 rounds)',
  ],
  [
    'one EXTERNAL round (16 S-boxes + layer)',
    await marginalRows(async (n) => {
      for (let i = 0; i < n; i++) probeExternalRound(w16()).forEach((x) => x.seal());
    }),
    '8 per permutation',
  ],
  [
    'one INTERNAL round (1 S-box + diag + 16 re-bounds)',
    await marginalRows(async (n) => {
      for (let i = 0; i < n; i++) probeInternalRound(w16()).forEach((x) => x.seal());
    }),
    '13 per permutation',
  ],
];
for (const [name, rows, note] of parts)
  console.log(`    ${name.padEnd(52)} ${String(rows).padStart(5)}  (${note})`);

// The figure a Pickles step actually pays: a ZkProgram carries public-input rows
// and zk_rows on top of the raw gate count.
const P2Program = ZkProgram({
  name: 'poseidon2-babybear-w16-perm',
  publicOutput: Provable.Array(Field, 16),
  methods: {
    onePerm: {
      privateInputs: [Provable.Array(Field, 16)],
      async method(input: Field[]) {
        return { publicOutput: provablePerm(input) };
      },
    },
  },
});
const analysis = await P2Program.analyzeMethods();
console.log(`    as a ZkProgram method: ${analysis.onePerm.rows.toLocaleString()} rows`);

// ---------------------------------------------------------------------------
// 3c. A row count is a claim about a circuit that COMPILES. Prove one.
// ---------------------------------------------------------------------------
console.log('\n[3c] the circuit is really Pickles-provable (not just countable)');
{
  const t0 = Date.now();
  await P2Program.compile();
  ok(`compiled a 1-permutation ZkProgram in ${((Date.now() - t0) / 1000).toFixed(1)}s`);
  const t1 = Date.now();
  const { proof } = await P2Program.onePerm([...Array(16).keys()].map((i) => Field(i)));
  ok(`proved it in ${((Date.now() - t1) / 1000).toFixed(1)}s`);
  if (!(await P2Program.verify(proof))) fail('the permutation proof failed to verify');
  ok('the proof VERIFIES');
  const out = proof.publicOutput.map((f) => f.toBigInt() % P);
  if (!eqv(out, KAT_RANGE16))
    fail(`the PROVEN output ${out} is not the deployed permutation's`);
  ok('the PROVEN public output == the deployed permutation on [0..15]');
}

// ---------------------------------------------------------------------------
// 3d. Ratchet: the number in the document must stay the number here.
// ---------------------------------------------------------------------------
const RECORDED_ROWS_PER_PERM = 2600.5; // docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.4, measured 2026-07-28
const drift = Math.abs(marginal - RECORDED_ROWS_PER_PERM) / RECORDED_ROWS_PER_PERM;
if (drift > 0.02)
  fail(
    `rows/permutation moved to ${marginal} from the recorded ${RECORDED_ROWS_PER_PERM} ` +
      `(${(drift * 100).toFixed(1)}%): docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.4 and its ` +
      'totals are now stale — update both, or the document is quoting a number nothing produces',
  );
console.log(
  `\n    ratchet: ${marginal} rows/perm is within 2% of the recorded ${RECORDED_ROWS_PER_PERM}`,
);

// ---------------------------------------------------------------------------
// 4. Re-derive the document's totals from the MEASURED number.
// ---------------------------------------------------------------------------
const DESIGN_CLAIM = 2000; //           MINA-VERIFIES-DREGG-FRI-SIZE.md §3.4
const GNARK_PARITY = 8400; //           §3.7, the pessimistic band end
const PERMS_LOW = 10250; //             §2.2, structural re-derivation
const PERMS_CENTRAL = 11000; //         §2.1, the measured in-tree count
const PERMS_HIGH = 13000; //            §2.1, the top of the measured range
const KIMCHI_ROWS = 65536; //           2^16, the Pickles step domain
const USABLE_LOW = 48000; //            §4.1, measured overheads
const USABLE_HIGH = 55000;

console.log('\n[4] totals re-derived at the MEASURED rows/permutation');
console.log(
  `    design claim ${DESIGN_CLAIM.toLocaleString()} rows/perm -> measured ` +
    `${marginal.toLocaleString()} = ${(marginal / DESIGN_CLAIM).toFixed(2)}x the claim`,
);
console.log(
  `    gnark-emulation parity ${GNARK_PARITY.toLocaleString()} -> measured is ` +
    `${(GNARK_PARITY / marginal).toFixed(2)}x CHEAPER than that end of the band`,
);
console.log('');
console.log('    perms/root-verify   total rows        Pickles steps (48k/55k usable)');
for (const [label, perms] of [
  ['low  (§2.2)', PERMS_LOW],
  ['central (§2.1)', PERMS_CENTRAL],
  ['high (§2.1)', PERMS_HIGH],
] as [string, number][]) {
  const total = perms * marginal;
  console.log(
    `    ${label.padEnd(18)} ${perms.toLocaleString().padStart(6)} ` +
      `${total.toExponential(2).padStart(12)}  ` +
      `${Math.ceil(total / USABLE_HIGH)}–${Math.ceil(total / USABLE_LOW)}`,
  );
}
console.log(
  `    (ceiling check: ${Math.floor(KIMCHI_ROWS / marginal)} permutations fit in one 2^16 step)`,
);

console.log('\n=== PASS ===\n');
