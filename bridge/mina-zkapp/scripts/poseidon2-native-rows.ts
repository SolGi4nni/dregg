import { Field, Provable } from 'o1js';
import {
  loadEmittedPerm,
  checkWitnessWeld,
  solveWitness,
  replayEmitted,
  provablePermNative,
  type EmittedPerm,
} from '../src/Poseidon2Native.js';
import { permBigInt, provablePermBounded, P, LANE_BOUND } from '../src/Poseidon2BabyBearW16.js';
import { atTier, tierStop } from '../src/tier.js';

// ---------------------------------------------------------------------------
// THE DIFFERENTIAL BETWEEN A GENERATED PERMUTATION AND A HAND-WRITTEN ONE.
//
// `poseidon2-babybear-rows` measures the HAND-WRITTEN o1js circuit against the
// bigint reference. This leg measures the LEAN-EMITTED one against BOTH — the
// reference AND the hand-written circuit — because the interesting question is
// not "does the generated circuit compute Poseidon2" (Lean `#guard`s that over
// its own emitted rows) but "does transcribing it into o1js preserve what Lean
// proved, and at what price".
//
// ⚑ THE ROW COMPARISON IS THE POINT AND IT IS NOT EXPECTED TO MATCH. Lean pins
// 2,669; o1js measures the hand-written one at 2,602. A transcriber that lands
// on Lean's number has preserved the emission; one that lands on o1js's has
// silently let o1js's compiler re-decide the circuit, which would make every
// row theorem on the Lean side a statement about a different object.
// ---------------------------------------------------------------------------

const t0 = Date.now();
const el = () => `${((Date.now() - t0) / 1000).toFixed(1)}s`;
let checks = 0;
const fail = (m: string) => {
  console.error(`FAIL: ${m}`);
  process.exit(1);
};
const ok = (m: string) => {
  checks++;
  console.log(`  ok  ${m}`);
};

// ── [0] the artifact loads and is self-consistent ──────────────────────────
console.log('[0] the emitted artifact');
let prog: EmittedPerm;
try {
  prog = loadEmittedPerm();
} catch (e) {
  fail(`${(e as Error).message}`);
  throw e;
}
console.log(
  `    ${prog.air}\n    source ${prog.source}\n` +
    `    ${prog.subGates} instructions, ${prog.kimchiRows} Kimchi rows, ${prog.nVars} variables`
);
if (prog.width !== 16) fail(`width ${prog.width}, expected 16`);
if (BigInt(prog.modulus) !== P) fail(`artifact modulus ${prog.modulus} is not BabyBear ${P}`);
ok(`width 16 over BabyBear p = ${P}`);

const nGen = prog.prog.filter((o) => o.k === 'g').length;
const nRc = prog.prog.filter((o) => o.k === 'r').length;
ok(`instruction mix: ${nGen} generic sub-gates, ${nRc} RangeCheck0 rows`);

// ⚑ The transcriber must be told about every shape the artifact carries, or it
// drops constraints silently. An unknown `k` is a refusal, not a skip.
const unknown = prog.prog.filter((o) => o.k !== 'g' && o.k !== 'r' && o.k !== 'z');
if (unknown.length > 0) fail(`${unknown.length} instructions of a shape this transcriber cannot emit`);
ok('every emitted instruction is a shape the transcriber emits');

// ── [1] the witness weld: an independent solver reproduces Lean's own witness ─
console.log('\n[1] the witness weld (TS solver vs Lean `honestVals`)');
const weld = checkWitnessWeld(prog);
if (weld.mismatches.length > 0) {
  console.error(weld.mismatches.slice(0, 10).join('\n'));
  fail(
    `${weld.mismatches.length} of ${weld.checked} witness values disagree with Lean. The solver ` +
      'reads only the emitted coefficients, so a disagreement means the TypeScript is telling a ' +
      'different story about the same circuit.'
  );
}
ok(`all ${weld.checked} witness values agree with Lean's generator`);

// ── [2] the KAT crossing: the solved witness computes the deployed permutation ─
console.log('\n[2] the KAT');
const katIn = prog.honestInput.map(BigInt);
const { w } = solveWitness(prog, katIn);
const solvedOut = prog.outputVars.map((v) => w[v] % P);
const refOut = permBigInt(katIn);
if (solvedOut.length !== 16 || solvedOut.some((x, i) => x !== refOut[i])) {
  fail(
    `the emitted circuit's output lanes are not the deployed permutation's.\n` +
      `  emitted: ${solvedOut.join(',')}\n  reference: ${refOut.join(',')}`
  );
}
ok('output lanes (canonical) == permBigInt(0..15), the deployed KAT');

const artOut = prog.honestOutput.map(BigInt);
if (artOut.some((x, i) => x !== refOut[i])) fail("the artifact's own honestOutput is not the KAT");
ok("the artifact's recorded output agrees with the reference");

// ⚑ The output lanes are NOT bounded by 2^31 and the artifact says so. A caller
// that re-feeds one without reducing is unsound, and this is where that is
// checked rather than commented.
const bounds = prog.outputBounds.map(BigInt);
if (bounds.some((b) => b <= LANE_BOUND)) {
  fail('an output lane claims a bound at or under LANE_BOUND — the closing external layer fans in 35x');
}
ok(`every output lane bound exceeds LANE_BOUND (max ${bounds.reduce((a, b) => (a > b ? a : b))})`);

// ── [3] TAMPER: a bent coefficient must break the witness ───────────────────
console.log('\n[3] the tamper (a bent coefficient must refuse)');
{
  const bent: EmittedPerm = {
    ...prog,
    prog: prog.prog.map((o, i) => (i === prog.subGates - 1 && o.k === 'g' ? { ...o, cc: o.cc + 1 } : o)),
  };
  const last = bent.prog[bent.subGates - 1];
  if (last.k !== 'g') {
    fail('the last instruction is not a generic sub-gate; re-aim the tamper at one that is');
  }
  const { violated } = solveWitness(bent, katIn);
  const bentOut = solveWitness(bent, katIn).w[prog.outputVars[15]] % P;
  if (violated.length === 0 && bentOut === refOut[15]) {
    fail(
      'bending the last emitted coefficient changed NEITHER the witness NOR any constraint — ' +
        'the transcriber is not reading the coefficients it claims to read.'
    );
  }
  ok(`a bent coefficient moves the emission (violations ${violated.length}, lane 15 ${bentOut !== refOut[15] ? 'moved' : 'held'})`);
}

if (!atTier(1)) {
  tierStop(
    'POSEIDON2-NATIVE',
    checks,
    el(),
    'the in-circuit replay (Provable.runAndCheck), the row measurement against the artifact\'s ' +
      'kimchiRows, and the head-to-head against the hand-written provablePermBounded. Tier 1 runs them.'
  );
  process.exit(0);
}

// ── [4] the in-circuit replay agrees with the reference ─────────────────────
console.log('\n[4] the in-circuit replay');
await Provable.runAndCheck(() => {
  const lanes = Provable.witness(Provable.Array(Field, 16), () =>
    katIn.map((x) => Field(x))
  );
  const out = provablePermNative(lanes);
  Provable.asProver(() => {
    const got = out.map((f) => f.toBigInt() % P);
    if (got.some((x, i) => x !== refOut[i])) {
      throw new Error(`in-circuit replay diverged from the KAT: ${got.join(',')}`);
    }
  });
});
ok('Provable.runAndCheck accepts the replay and it computes the KAT');

// ── [5] rows: the transcription must land on LEAN'S number, not o1js's ──────
console.log('\n[5] rows');
const csNative = await Provable.constraintSystem(() => {
  const lanes = Provable.witness(Provable.Array(Field, 16), () => katIn.map((x) => Field(x)));
  provablePermNative(lanes);
});
const csHand = await Provable.constraintSystem(() => {
  const lanes = Provable.witness(Provable.Array(Field, 16), () => katIn.map((x) => Field(x)));
  provablePermBounded(lanes, P - 1n);
});
console.log(`    Lean-emitted, transcribed : ${csNative.rows} rows (artifact predicts ${prog.kimchiRows})`);
console.log(`    hand-written o1js          : ${csHand.rows} rows`);
console.log(
  `    delta                      : ${csNative.rows - csHand.rows} ` +
    `(${(((csNative.rows - csHand.rows) / csHand.rows) * 100).toFixed(2)}%)`
);

// The 16 spliced input lanes are the caller's variables, so the replay may seal
// a few of them; anything beyond that means o1js re-decided the circuit.
const slack = 20;
if (Math.abs(csNative.rows - prog.kimchiRows) > slack) {
  fail(
    `the transcription measured ${csNative.rows} rows where Lean's emission is ${prog.kimchiRows}. ` +
      'A gap this size means o1js\'s compiler re-decided the circuit, which would make every row ' +
      'theorem on the Lean side a statement about a different object.'
  );
}
ok(`transcription lands on Lean's emitted row count within ${slack} (input-lane sealing)`);

console.log(`\n=== POSEIDON2-NATIVE PASS === ${checks} checks, ${el()}`);
console.log(
  `    ratchet: emitted ${prog.kimchiRows} rows, transcribed ${csNative.rows}, ` +
    `hand-written ${csHand.rows}`
);
