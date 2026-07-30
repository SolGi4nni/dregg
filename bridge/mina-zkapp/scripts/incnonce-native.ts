import { Field, Provable, verify } from 'o1js';
import {
  DreggIncNonceNative,
  EMITTED,
  IncNonceRow,
  PRE_COLS,
  POST_COLS,
  baseAssignment,
  checkWitnessWeld,
  claimDigest,
  solveWitness,
  witnessAndReplay,
  type RowSpec,
} from '../src/DreggIncNonceNative.js';

// ---------------------------------------------------------------------------
// ROUTE B, RUN FOR REAL: compile, prove, verify, then TAMPER.
//
// Every constraint in the circuit came out of Lean
// (`Dregg2.Circuit.Emit.KimchiEffectIncNonce.emitJson`). This script measures it
// and exercises it; it authors nothing either.
//
// The instances are the ones the Lean file already carries as non-vacuity
// witnesses, so the Lean theorem and the o1js run are talking about the SAME
// rows:
//
//   goodIncNonceRow          bal_lo 100 -> 100, nonce 5 -> 6        MUST prove
//   badIncNonceRow           post bal_lo minted to 999              MUST refuse
//   staleNonceIncNonceRow    post nonce held at 5                   MUST refuse
//   wrong selector           the right SHAPE, col 53 = 0            MUST refuse
//
// The last one is what `selectorBindHead` bought: without it the circuit checks
// the shape "economic block frozen, nonce ticked" and ANY effect with that shape
// satisfies it. With it, the proof is about `incrementNonceA`.
// ---------------------------------------------------------------------------

function block(balLo: bigint, balHi: bigint, nonce: bigint): bigint[] {
  // [balLo, balHi, nonce, field0..7, capRoot, reserved] — the order
  // `PRE_COLS`/`POST_COLS` were built in, which came from the emitted column map.
  return [balLo, balHi, nonce, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n];
}

/** `EffectVmEmitIncrementNonce.goodIncNonceRow` — the honest row. */
const GOOD: RowSpec = {
  preBlock: block(100n, 0n, 5n),
  postBlock: block(100n, 0n, 6n),
  selectorSet: 1n,
};
/** `badIncNonceRow` — post-balance minted to 999. */
const MINTED: RowSpec = { ...GOOD, postBlock: block(999n, 0n, 6n) };
/** `staleNonceIncNonceRow` — the nonce does not tick. */
const STALE: RowSpec = { ...GOOD, postBlock: block(100n, 0n, 5n) };
/** The right SHAPE under someone else's selector — what `selectorBindHead` exists to refuse. */
const WRONG_SELECTOR: RowSpec = { ...GOOD, selectorSet: 0n };

function toRow(spec: RowSpec): IncNonceRow {
  return new IncNonceRow({
    preBlock: spec.preBlock.map((x) => Field(x)),
    postBlock: spec.postBlock.map((x) => Field(x)),
    selectorSet: Field(spec.selectorSet),
  });
}

function ms(t: number): string {
  return `${(t / 1000).toFixed(2)}s`;
}

console.log('== ROUTE B: dregg semantics emitted into Kimchi ==');
console.log(`air                : ${EMITTED.air}`);
console.log(`lean source        : ${EMITTED.source}`);
console.log(`emitted sub-gates  : ${EMITTED.subGates}`);
console.log(`predicted rows     : ${EMITTED.kimchiRows}   (KimchiEffectIncNonce.incNonceKimchiRows_length)`);
console.log('');

// ---------------------------------------------------------------------------
// 0a. The TS witness solver reproduces LEAN'S OWN witness, variable for variable.
// ---------------------------------------------------------------------------
const weld = checkWitnessWeld(EMITTED);
console.log(
  `witness weld vs Lean satAssign          : ${
    weld.mismatches.length === 0 ? `AGREES on all ${weld.checked} intermediates` : 'MISMATCH'
  }`
);
for (const m of weld.mismatches) console.log(`  ${m}`);
if (weld.mismatches.length > 0) {
  throw new Error('the TypeScript witness solver disagrees with Lean about the honest witness');
}

// And the driver's own hand-written honest row must be Lean's row.
{
  const mine = baseAssignment(EMITTED, GOOD);
  const theirs = new Array<bigint>(EMITTED.firstFreshVar).fill(0n);
  for (const [c, v] of EMITTED.honestBase) theirs[c] = BigInt(v);
  const diff = mine.map((x, i) => (x === theirs[i] ? null : i)).filter((i) => i !== null);
  console.log(
    `driver row vs Lean goodIncNonceRow      : ${
      diff.length === 0 ? 'IDENTICAL' : `DIFFERS at columns [${diff}]`
    }`
  );
  if (diff.length !== 0) throw new Error('the driver is not exercising the row Lean proved about');
}
console.log('');

// ---------------------------------------------------------------------------
// 0b. The witness solver agrees with Lean about which rows are valid.
// ---------------------------------------------------------------------------
for (const [name, spec, expectValid] of [
  ['goodIncNonceRow', GOOD, true],
  ['badIncNonceRow', MINTED, false],
  ['staleNonceIncNonceRow', STALE, false],
  ['wrong selector (col 53 = 0)', WRONG_SELECTOR, false],
] as const) {
  const { violated } = solveWitness(EMITTED, baseAssignment(EMITTED, spec));
  const ok = violated.length === 0;
  console.log(
    `solver ${name.padEnd(28)}: ${ok ? 'SATISFIED' : `VIOLATED at sub-gates [${violated}]`}` +
      `${ok === expectValid ? '' : '   <-- UNEXPECTED'}`
  );
  if (ok !== expectValid) {
    throw new Error(`solver disagrees with Lean on ${name}`);
  }
}
console.log('');

// ---------------------------------------------------------------------------
// 1. Rows of the SEMANTIC CORE — the emitted sub-gates and nothing else.
// ---------------------------------------------------------------------------
const solved = solveWitness(EMITTED, baseAssignment(EMITTED, GOOD)).w;
const coreCs = await Provable.constraintSystem(() => {
  witnessAndReplay(EMITTED, () => solved);
});
console.log(`core rows (transcribed sub-gates only) : ${coreCs.rows}`);
const hist = coreCs.gates.reduce<Record<string, number>>((acc, g) => {
  acc[g.type] = (acc[g.type] ?? 0) + 1;
  return acc;
}, {});
console.log(`core gate histogram                    : ${JSON.stringify(hist)}`);
console.log('');

// ---------------------------------------------------------------------------
// 2. Compile the full program (public binding + range checks).
// ---------------------------------------------------------------------------
const analysis = await DreggIncNonceNative.analyzeMethods();
console.log(`full method rows                       : ${analysis.check.rows}`);

let t = Date.now();
const { verificationKey } = await DreggIncNonceNative.compile();
const compileMs = Date.now() - t;
console.log(`compile                                : ${ms(compileMs)}`);
console.log(`vk hash                                : ${verificationKey.hash.toString()}`);
console.log('');

// ---------------------------------------------------------------------------
// 3. PROVE the honest transition, and VERIFY the proof object.
// ---------------------------------------------------------------------------
t = Date.now();
const { proof } = await DreggIncNonceNative.check(claimDigest(GOOD), toRow(GOOD));
const proveMs = Date.now() - t;
console.log(`prove (goodIncNonceRow)                : ${ms(proveMs)}`);

t = Date.now();
const ok = await verify(proof, verificationKey);
const verifyMs = Date.now() - t;
console.log(`verify                                 : ${ok} in ${ms(verifyMs)}`);
if (!ok) throw new Error('the honest transition did not verify — route B is broken');
console.log('');

// ---------------------------------------------------------------------------
// 4. TAMPER. Each must be REFUSED, with a real proof attempt, not a pre-check.
// ---------------------------------------------------------------------------
for (const [name, spec] of [
  ['badIncNonceRow (post bal_lo = 999)', MINTED],
  ['staleNonceIncNonceRow (nonce frozen)', STALE],
  ['wrong selector (right shape, col 53 = 0)', WRONG_SELECTOR],
] as const) {
  let refused = false;
  let why = '';
  try {
    await DreggIncNonceNative.check(claimDigest(spec), toRow(spec));
  } catch (e) {
    refused = true;
    why = (e as Error).message.split('\n')[0].slice(0, 120);
  }
  console.log(`tamper ${name.padEnd(42)}: ${refused ? `REFUSED (${why})` : 'ACCEPTED  <-- HOLE'}`);
  if (!refused) {
    throw new Error(`the emitted circuit ACCEPTED an invalid transition: ${name}`);
  }
}
console.log('');

// ---------------------------------------------------------------------------
// 5. And a forged proof object must not verify against the honest statement.
// ---------------------------------------------------------------------------
const forgedClaim = claimDigest(MINTED);
const forged = await proof.toJSON();
forged.publicInput = [forgedClaim.toString()];
let forgeVerified = false;
try {
  const reimported = await DreggIncNonceNative.Proof.fromJSON(forged);
  forgeVerified = await verify(reimported, verificationKey);
} catch {
  forgeVerified = false;
}
console.log(`re-pointed public input verifies       : ${forgeVerified}${forgeVerified ? '  <-- HOLE' : ''}`);
if (forgeVerified) throw new Error('a proof verified against a public input it does not prove');

console.log('');
console.log('== route B: honest transition proved and verified; all three tampers refused ==');
console.log(
  `== predicted ${EMITTED.kimchiRows} rows from Lean, measured ${coreCs.rows} for the core ==`
);
