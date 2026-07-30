import { Field, Provable } from 'o1js';
import { readFileSync, existsSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  claimOf,
  makeDreggProofClaim,
  makeDreggProofVerifyProgram,
  minaFixtureConstraints,
  minaFixtureConstraintsBentDegree,
  minaFixtureConstraintsNoSelector,
  minaFixtureConstraintsPermuted,
  shapeOf,
  suiteOf,
  witnessOf,
} from '../src/DreggProofVerify.js';
import { PastaChallengerBigInt } from '../src/PastaChallenger.js';
import { P_PASTA } from '../src/PastaMmcs.js';

// ---------------------------------------------------------------------------
// ⚑ THE LEVER, PULLED: the o1js side CONSUMES a real Pasta-hashed dregg proof.
//
// `DreggMinaConfig` landed a config that lets dregg MINT a proof whose MMCS
// commits with kimchi's own Poseidon over Pasta Fp. Its own doc named the gap:
// "a config that nothing consumes is a lever built, not pulled" —
// `Poseidon2Merkle.ts` still hashed Poseidon2-BabyBear and nothing on Mina could
// take a Mina-native proof. This script is the other end.
//
// The proof is minted by `circuit-prove/src/bin/mina_pasta_stark_fixture.rs`,
// which runs `p3_uni_stark::prove` under `DreggMinaConfig` and then
// `p3_uni_stark::verify` — DREGG'S OWN VERIFIER ACCEPTS BEFORE ANYTHING IS
// EMITTED, so a fixture that reaches here is one dregg itself accepts.
//
// WHAT IS SHOWN, in order, and why that order:
//
//   [1] THE TRANSCRIPT, PERMUTATION BY PERMUTATION. The emitter records p3's own
//       `MultiField32Challenger` sponge state after EVERY permutation and every
//       observe/sample event. The o1js twin replays the log and must match at
//       each one. This is checked FIRST and out of circuit, because a transcript
//       that is wrong in the fourth permutation still compiles, still proves, and
//       still produces a beautiful row count — it just proves a different
//       protocol.
//   [2] THE WALK, out of circuit then in circuit, on the real proof.
//   [3] PROVED with the real Pickles prover, and VERIFIED.
//   [4] REFUSED: every tamper fixture, and every bent constraint reading.
//   [5] The BabyBear twin at the SAME geometry, so the swap's o1js-side price is
//       a measurement of one object under two hashes rather than two numbers.
//
//   npm run pasta-verify
// ---------------------------------------------------------------------------

const DIR = process.env.PASTA_FIXTURE_DIR ?? resolve(process.cwd(), '.pasta-fixtures');
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');

let failures = 0;
function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  failures++;
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
function check(cond: boolean, msg: string) {
  if (cond) ok(msg);
  else fail(msg);
}

function load(name: string): any {
  const p = resolve(DIR, name);
  if (!existsSync(p))
    throw new Error(
      `the Pasta fixture ${p} is missing. Mint it with:\n` +
        `  cargo run -p dregg-circuit-prove --release --bin mina_pasta_stark_fixture -- 3 1 2 16 1 none`,
    );
  return JSON.parse(readFileSync(p, 'utf8'));
}

console.log('=== o1js CONSUMES A PASTA-HASHED DREGG PROOF ===\n');

// ---------------------------------------------------------------------------
// [1] The transcript, against p3's own state machine.
// ---------------------------------------------------------------------------
function replayTranscript(fx: any, label: string) {
  const log = fx.challenges.transcript as any[];
  const states = (fx.challenges.spongeStates as string[][]).map((s) => s.map(BigInt));
  const c = new PastaChallengerBigInt();
  let permIdx = 0;
  let sampled = 0;
  const seenState = () => {
    // Compare after every permutation the twin performs, in order.
    while (permIdx < c.perms) {
      const want = states[permIdx];
      if (!want) fail(`${label}: the twin permuted ${c.perms} times, p3 recorded ${states.length}`);
      if (c.perms - 1 === permIdx) {
        for (let j = 0; j < 3; j++)
          if (c.state[j] !== want[j])
            fail(
              `${label}: sponge state diverges at permutation ${permIdx}, lane ${j}\n` +
                `      p3  ${want[j]}\n      o1js ${c.state[j]}`,
            );
      }
      permIdx++;
    }
  };

  for (const ev of log) {
    switch (ev.op) {
      case 'observeF':
        c.observe(BigInt(ev.v));
        break;
      case 'observeDigest':
        c.observeDigest((ev.w as string[]).map(BigInt));
        break;
      case 'sampleExt': {
        const got = c.sampleExt();
        const want = (ev.v as number[]).map(BigInt);
        for (let j = 0; j < 4; j++)
          if (got[j] !== want[j])
            fail(`${label}: sampled extension challenge #${sampled} limb ${j} — p3 ${want[j]}, o1js ${got[j]}`);
        sampled++;
        break;
      }
      case 'checkWitness': {
        const passed = c.checkWitness(ev.bits, BigInt(ev.w));
        if (!passed && fx.tamper === 'none')
          fail(`${label}: the ${ev.bits}-bit PoW check FAILED on an honest fixture`);
        break;
      }
      case 'sampleBits': {
        const got = c.sampleBits(ev.bits);
        if (got !== ev.v) fail(`${label}: sample_bits(${ev.bits}) — p3 ${ev.v}, o1js ${got}`);
        break;
      }
      default:
        fail(`${label}: unknown transcript op '${ev.op}'`);
    }
    seenState();
  }
  check(
    permIdx === states.length,
    `${label}: ${log.length} transcript events, ${permIdx} permutations, EVERY sponge state and EVERY sampled challenge matches p3's MultiField32Challenger`,
  );
  return c;
}

// ---------------------------------------------------------------------------
/** Constraint satisfaction only — sound for a REFUSAL (an unsatisfied
 *  constraint is unsatisfied), never quoted as an accept without a `prove`. */
async function satisfies(fx: any, cons: any): Promise<boolean> {
  const sh = shapeOf(fx, { constraints: cons });
  const { prog, DreggProofClaim } = makeDreggProofVerifyProgram(sh);
  const claim = claimOf(fx, DreggProofClaim);
  const w = witnessOf(fx, sh);
  const types = (prog as any).privateInputTypes.verifyDreggProof;
  try {
    await Provable.runAndCheck(async () => {
      const c = Provable.witness(DreggProofClaim, () => claim);
      const pw = w.map((v: any, i: number) => Provable.witness(types[i], () => v));
      await (prog as any).rawMethods.verifyDreggProof(c, ...pw);
    });
    return true;
  } catch {
    return false;
  }
}

async function main() {
  const fxSmall = load('honest-d2-q1.json');
  const fx = load('honest-d3-q2.json');
  const fxBb = load('bb-honest-d3-q2.json');
  const TAMPERS = ['opened', 'quotient', 'finalpoly', 'sibling', 'inputrow', 'inputpath', 'querypow'];
  const tamperFx = (t: string) => {
    const p = resolve(DIR, `tamper-${t}.json`);
    return existsSync(p) ? JSON.parse(readFileSync(p, 'utf8')) : null;
  };

  console.log('[1] THE TRANSCRIPT, permutation by permutation, against p3');
  check(fx.hash === 'mina-poseidon-pasta', `the fixture says it was minted under '${fx.hash}'`);
  check(suiteOf(fx).name === 'mina-poseidon-pasta', 'and `suiteOf` routes it to the Pasta suite BY NAME');
  check(suiteOf(fxBb).name === 'poseidon2-babybear-w16', 'while the BabyBear fixture routes to the BabyBear suite');
  const rootBits = BigInt(fx.commitments.trace[0][0]).toString(2).length;
  check(
    rootBits > 31,
    `the trace commitment is a NATIVE Pasta element (${rootBits} bits — a BabyBear digest word is always <= 31)`,
  );
  check(BigInt(fx.commitments.trace[0][0]) < P_PASTA, 'and it is canonical');
  replayTranscript(fxSmall, 'd2-q1');
  replayTranscript(fx, 'd3-q2');
  let bentReplays = 0;
  for (const t of TAMPERS) {
    const b = tamperFx(t);
    if (b) {
      replayTranscript(b, `tamper-${t}`);
      bentReplays++;
    }
  }
  ok(`and on all ${bentReplays} BENT fixtures too — the twin tracks p3 through a transcript p3 itself rejects`);

  // -------------------------------------------------------------------------
  console.log('\n[2] THE WALK, in circuit, on the real proof');
  const sh = shapeOf(fx, { constraints: minaFixtureConstraints });
  console.log(
    `    shape: degree_bits ${sh.air.degreeBits}, ${sh.knobs.numQueries} queries, ${sh.knobs.layers} fold ` +
      `layers, |D^0| = 2^${sh.logGlobalMaxHeight}, ${sh.air.width} AIR columns, ` +
      `${sh.air.numQuotientChunks} quotient chunks, input path depth ${sh.batches[0].pathDepth}`,
  );
  const { prog, DreggProofClaim } = makeDreggProofVerifyProgram(sh);
  const claim = claimOf(fx, DreggProofClaim);
  const wit = witnessOf(fx, sh);
  const a = await prog.analyzeMethods();
  const pastaRows = (a as any).verifyDreggProof.rows;
  console.log(`    the Pasta walk is ${fmt(pastaRows)} rows`);
  check(await satisfies(fx, minaFixtureConstraints), 'the constraints are SATISFIED by the real Pasta proof');

  // -------------------------------------------------------------------------
  console.log('\n[3] PROVED and VERIFIED with the real Pickles prover');
  let t0 = Date.now();
  await prog.compile();
  console.log(`    compile ${((Date.now() - t0) / 1000).toFixed(1)}s`);
  t0 = Date.now();
  const { proof } = await (prog as any).verifyDreggProof(claim, ...wit);
  console.log(`    prove   ${((Date.now() - t0) / 1000).toFixed(1)}s`);
  check(await prog.verify(proof), 'the o1js proof of "this Pasta-hashed dregg proof verifies" VERIFIES');
  const derivedIdx = (proof.publicOutput as any[]).map((f) => Number(f.toBigInt()));
  check(
    String(derivedIdx) === String(fx.challenges.queryIndices),
    `the PROVEN query indices [${derivedIdx.join(', ')}] are the ones p3's own MultiField32Challenger drew — the walk went where the transcript sent it, not where a witness said`,
  );

  // -------------------------------------------------------------------------
  console.log('\n[4] REFUSED — and each refusal is a real prove() refusal');
  // dregg's OWN verifier already refused each bend (the emitter asserts it
  // before emitting), so an o1js accept here would be a hole in THIS verifier
  // and nowhere else.
  const WHAT: Record<string, string> = {
    opened: 'a claimed out-of-domain evaluation',
    quotient: 'a quotient chunk',
    finalpoly: 'the final polynomial',
    sibling: 'a commit-phase sibling',
    inputrow: 'an input-phase opened row element',
    inputpath: 'an input-phase Merkle sibling',
    querypow: 'the query PoW witness',
  };
  for (const t of TAMPERS) {
    const bent = tamperFx(t);
    if (!bent) fail(`the '${t}' tamper fixture is missing`);
    if (bent.tamper !== t) fail(`fixture tamper-${t}.json says tamper '${bent.tamper}'`);
    let refused = false;
    try {
      await (prog as any).verifyDreggProof(claimOf(bent, DreggProofClaim), ...witnessOf(bent, sh));
    } catch {
      refused = true;
    }
    if (!refused) fail(`the o1js verifier ACCEPTED a proof with ${WHAT[t]} bent`);
    ok(`prove() REFUSES ${WHAT[t]}`);
  }

  // The AIR closing equality, watched saying no. Same proof, same transcript,
  // same openings, same fold chain — only the constraint evaluator moves, so a
  // refusal is attributable to the AIR check and to nothing else.
  for (const [name, ev] of [
    ['a^2 where dregg proved a^3', minaFixtureConstraintsBentDegree],
    ['C_1 and C_3 swapped — the FOLD ORDER', minaFixtureConstraintsPermuted],
    ['is_transition dropped from C_2', minaFixtureConstraintsNoSelector],
  ] as const) {
    if (await satisfies(fx, ev)) fail(`the closing equality ACCEPTED '${name}'`);
    ok(`the AIR closing equality REFUSES '${name}'`);
  }
  if (!(await satisfies(fx, undefined)))
    fail('the PCS-only statement refuses the honest proof — the control is broken');
  ok('and the PCS-only statement (no AIR check) ACCEPTS the same proof — the control holds');

  // ⚑ THE CROSS-HASH REFUSAL. A BabyBear-hashed fixture handed to the Pasta walk
  // must be refused BY NAME, at shape time, not discovered as a digest mismatch
  // forty thousand rows in.
  {
    let msg = 'ACCEPTED';
    try {
      shapeOf({ ...fxBb, hash: 'mina-poseidon-pasta' }, { constraints: minaFixtureConstraints });
    } catch (e: any) {
      msg = e.message;
    }
    check(msg !== 'ACCEPTED', `a BabyBear fixture RELABELLED as Pasta is refused: "${msg.slice(0, 90)}"`);
    let msg2 = 'ACCEPTED';
    try {
      shapeOf({ ...fx, hash: 'poseidon2-blake3-moonbeam' }, { constraints: minaFixtureConstraints });
    } catch (e: any) {
      msg2 = e.message;
    }
    check(msg2 !== 'ACCEPTED', 'and an unknown hash name is refused rather than silently defaulted');
  }

  // -------------------------------------------------------------------------
  console.log('\n[5] THE SAME PROOF SHAPE UNDER BOTH HASHES — the o1js-side price');
  const bsh = shapeOf(fxBb, { constraints: minaFixtureConstraints });
  const bb = makeDreggProofVerifyProgram(bsh);
  const bcs = await bb.prog.analyzeMethods();
  const bbRows = (bcs as any).verifyDreggProof.rows;
  check(
    await satisfies(fxBb, minaFixtureConstraints),
    'the BabyBear walk still accepts its own fixture — the shared refactor did not break it',
  );
  console.log(`    BabyBear-hashed walk : ${fmt(bbRows)} rows`);
  console.log(`    Pasta-hashed walk    : ${fmt(pastaRows)} rows`);
  console.log(`    ⚑ ${(bbRows / pastaRows).toFixed(1)}x fewer rows for the same statement about the same AIR`);
  console.log(
    `      ⚑ this ratio is a FLOOR, not the root's. At this toy geometry the hash-independent\n` +
      `        DEEP/AIR terms are a far larger share of the walk than at the root's 2^22 x 19\n` +
      `        queries; the root-geometry measurement is pasta-root-rows.ts.`,
  );

  if (failures > 0) {
    console.error(`\n${failures} FAILURES\n`);
    process.exit(1);
  }
  console.log('\n=== the Mina side CONSUMES a Pasta-hashed dregg proof, and REFUSES a bent one ===\n');
}

main().catch((e) => {
  console.error('\nFAILED:', e?.message ?? e, '\n');
  process.exit(1);
});
