import { Field, Provable, verify } from 'o1js';
import {
  COMMIT,
  DreggCellCommitNative,
  commitRows,
  useWitness,
  violatedGens,
  witnessVector,
  type WitnessMutation,
} from '../src/DreggCellCommitNative.js';
import { EMITTED, solveWitness } from '../src/DreggIncNonceNative.js';

// ---------------------------------------------------------------------------
// ROUTE B WITH THE COMMITMENT BINDING, RUN FOR REAL: measure, prove, verify,
// then TAMPER — with a pair that satisfies the ARITHMETIC and is NOT the
// pre-image of the claimed commitment. That refusal is the test that separates
// "checks a transition's arithmetic" from "checks a cell".
//
// Every constraint came out of Lean (`Dregg2.Circuit.Emit.KimchiCellCommit`),
// and so did the witness. This script measures it and exercises it; it authors
// nothing either.
//
// The instances:
//
//   honest            the cell bal 100 -> 100, nonce 5 -> 6,          MUST prove
//                     committed as H4(H4(100,0,6,0), H4(0^4), H4(0^4), 0)
//   substituted       the SAME valid transition, claiming a DIFFERENT   MUST refuse
//                     commitment (someone else's cell)
//   residue swapped   the SAME valid transition and the SAME claimed    MUST refuse
//                     commitment, with a different authority residue
//                     (aux 96) — the audit-P0-2 fourth GROUP-4 input
//
// For each tamper the script FIRST reports that the ARITHMETIC emission is
// still fully satisfied. That is the separation, exhibited: before the hash
// sites landed, both tampers were indistinguishable from the honest instance.
// ---------------------------------------------------------------------------

function ms(t: number): string {
  return `${(t / 1000).toFixed(2)}s`;
}

const HONEST_COMMIT = BigInt(COMMIT.honestCommit);
const STATE_COMMIT_VAR = COMMIT.cols.stateCommit;
const RECORD_DIGEST_VAR = COMMIT.cols.recordDigest;

console.log('== ROUTE B + GROUP-4 COMMITMENT BINDING ==');
console.log(`air                  : ${COMMIT.air}`);
console.log(`lean source          : ${COMMIT.source}`);
console.log(`emitted instructions : ${COMMIT.ops}`);
console.log(`witness variables    : ${COMMIT.vars}`);
console.log(`predicted rows       : sites ${COMMIT.siteRows} · commit ${COMMIT.commitRows} · route B ${COMMIT.routeBRows}`);
console.log(`absorbed columns     : ${JSON.stringify(COMMIT.siteInCols)}`);
console.log(`digest columns       : ${JSON.stringify(COMMIT.siteDigestCols)}`);
console.log(`honest cell commit   : ${HONEST_COMMIT}`);
console.log('');

// ---------------------------------------------------------------------------
// 0. The ARITHMETIC emission, evaluated on the honest row — the baseline every
//    tamper below is measured against.
// ---------------------------------------------------------------------------
function arithmeticViolations(mut?: WitnessMutation): number[] {
  const base = new Array<bigint>(EMITTED.firstFreshVar).fill(0n);
  for (const [col, v] of EMITTED.honestBase) base[col] = BigInt(v);
  if (mut && mut.var < EMITTED.firstFreshVar) base[mut.var] = mut.value;
  return solveWitness(EMITTED, base).violated;
}

console.log(`arithmetic on the honest row            : ${arithmeticViolations().length} violated`);

// ---------------------------------------------------------------------------
// 1. ROWS — the emitted count against what snarky reports.
// ---------------------------------------------------------------------------
let t = Date.now();
const measured = await commitRows();
console.log(`snarky rows for the commitment binding  : ${measured}`);
console.log(`Lean predicted                          : ${COMMIT.commitRows}`);
console.log(`delta                                   : ${measured - COMMIT.commitRows}   (${ms(Date.now() - t)})`);
console.log('');

// ---------------------------------------------------------------------------
// 2. COMPILE.
// ---------------------------------------------------------------------------
t = Date.now();
useWitness(witnessVector(COMMIT));
const { verificationKey } = await DreggCellCommitNative.compile();
console.log(`compile                                 : ${ms(Date.now() - t)}`);
console.log('');

// ---------------------------------------------------------------------------
// 3. HONEST — must prove and verify.
// ---------------------------------------------------------------------------
t = Date.now();
useWitness(witnessVector(COMMIT));
const honest = await DreggCellCommitNative.check(Field(HONEST_COMMIT));
console.log(`honest cell: prove                      : OK   (${ms(Date.now() - t)})`);
t = Date.now();
const ok = await verify(honest.proof, verificationKey);
console.log(`honest cell: verify                     : ${ok ? 'OK' : 'FAILED'}   (${ms(Date.now() - t)})`);
if (!ok) throw new Error('the honest cell did not verify — the binding is unusable');
console.log('');

// ---------------------------------------------------------------------------
// 4. TAMPERS — each must be REFUSED by a real prove().
// ---------------------------------------------------------------------------
async function mustRefuse(
  label: string,
  claim: bigint,
  muts: WitnessMutation[],
  arithmeticNote: string
): Promise<boolean> {
  console.log(`-- ${label}`);
  console.log(`   arithmetic emission                 : ${arithmeticNote}`);
  const w = witnessVector(COMMIT, muts);
  const broken = violatedGens(COMMIT.ops_, w);
  console.log(`   commitment sub-gates violated       : ${broken.length}` +
    (broken.length > 0 ? `  (first at instruction ${broken[0]})` : ''));
  useWitness(w);
  try {
    await DreggCellCommitNative.check(Field(claim));
    console.log('   prove()                             : ⚑ ACCEPTED — THIS IS A HOLE');
    return false;
  } catch (e) {
    const msg = e instanceof Error ? e.message.split('\n')[0] : String(e);
    console.log(`   prove()                             : REFUSED — ${msg.slice(0, 110)}`);
    return true;
  }
}

const refusals: boolean[] = [];

// 4a. A valid transition claiming SOMEONE ELSE'S commitment. The arithmetic is
//     untouched — column 88 is read by no arithmetic gate — so before the hash
//     sites this was indistinguishable from the honest instance.
const OTHER_COMMIT = HONEST_COMMIT + 1n;
refusals.push(
  await mustRefuse(
    'substituted commitment (a valid transition, someone else\'s commitment)',
    OTHER_COMMIT,
    [{ var: STATE_COMMIT_VAR, value: OTHER_COMMIT }],
    `${arithmeticViolations({ var: STATE_COMMIT_VAR, value: OTHER_COMMIT }).length} violated — STILL FULLY SATISFIED`
  )
);
console.log('');

// 4b. The SAME valid transition and the SAME claimed commitment, with a
//     different authority residue in the fourth GROUP-4 input (aux 96, audit
//     P0-2). No arithmetic gate reads it either.
refusals.push(
  await mustRefuse(
    'swapped authority residue (aux 96 — the fourth GROUP-4 input)',
    HONEST_COMMIT,
    [{ var: RECORD_DIGEST_VAR, value: 7n }],
    `${arithmeticViolations({ var: RECORD_DIGEST_VAR, value: 7n }).length} violated — STILL FULLY SATISFIED`
  )
);
console.log('');

// 4c. A forged INTERMEDIATE digest: claim the honest commitment while the first
//     GROUP-4 site's digest column carries a value the permutation did not
//     produce. This is the pin gate, directly.
refusals.push(
  await mustRefuse(
    'forged intermediate digest (aux 8 = inter1)',
    HONEST_COMMIT,
    [{ var: COMMIT.cols.inter1, value: 12345n }],
    `${arithmeticViolations({ var: COMMIT.cols.inter1, value: 12345n }).length} violated — STILL FULLY SATISFIED`
  )
);
console.log('');

// ---------------------------------------------------------------------------
// 5. VERDICT.
// ---------------------------------------------------------------------------
const allRefused = refusals.every((x) => x);
console.log('== VERDICT ==');
console.log(`honest cell proves and verifies         : yes`);
console.log(`every non-pre-image tamper refused      : ${allRefused ? 'yes' : 'NO'}`);
console.log(`rows: Lean ${COMMIT.commitRows} · snarky ${measured}`);
console.log('');
console.log('⚑ What a verified proof of this program says: the (pre, post) pair is a valid');
console.log('  incrementNonceA transition AND the post-state is the pre-image, under the');
console.log('  deployed GROUP-4 hash_4_to_1 tree, of the claimed commitment — a real dregg cell.');
console.log('⚑ What it does NOT say: that dregg\'s chain contains that cell. A well-formed');
console.log('  transition of a cell that never existed passes this program.');

if (!allRefused) {
  process.exitCode = 1;
}
