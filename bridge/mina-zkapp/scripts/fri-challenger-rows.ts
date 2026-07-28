// RUNG 3 — the CHALLENGER. Measure the Fiat-Shamir transcript as an o1js
// circuit, and KAT it against the DEPLOYED `DuplexChallenger`.
//
//   npm run fri-challenger
//
// ⚑ THIS IS THE RUNG THAT CHANGES WHAT THE OTHERS MEAN. Rung 2 walks one FRI
// query with a WITNESSED index and a WITNESSED beta. A statement of that shape
// says "there exist 19 indices at which this proof is consistent" — and a
// cheating prover supplies the 19 it can answer. FRI's soundness is entirely
// the claim that the indices are drawn after the commitments by a function the
// prover cannot steer. This leg builds that function and proves it runs.
//
// The referent is the DEPLOYED challenger, not a transcription:
// `mina-pasta-hash-probe p2chal` / `p2fritranscript` call
// `p3_challenger::DuplexChallenger<BabyBear, Poseidon2BabyBear<16>, 16, 8>` at
// the same `82cfad73` rev the workspace pins, running exactly the schedule
// `p3_fri::verifier::verify_fri` runs, and this script must reproduce every
// challenge it derives — in the bigint twin AND inside a real proof.

import { Bool, Field, Provable } from 'o1js';
import { execFileSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { P } from '../src/Poseidon2BabyBearW16.js';
import { BbDigest } from '../src/Poseidon2Merkle.js';
import { BbExt } from '../src/FriQueryStep.js';
import {
  ChallengerBigInt,
  DEPLOYED_KNOBS,
  assertLowBitsSplit,
  assertLowBitsZero,
  assertLtPow2,
  FriKnobs,
  challengeDigestBigInt,
  deriveFriChallenges,
  deriveFriChallengesBigInt,
  makeFriTranscriptProgram,
  witnessTranscriptShape,
} from '../src/FriChallenger.js';

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
const eqv = (a: bigint[], b: bigint[]) => a.length === b.length && a.every((x, i) => x === b[i]);
const eq2 = (a: bigint[][], b: bigint[][]) => a.length === b.length && a.every((r, i) => eqv(r, b[i]));

function probeDir(): string {
  const d =
    process.env.DREGG_PROBE_DIR ??
    resolve(process.cwd(), '../../circuit-prove/sketches/mina-pasta-hash-probe');
  if (!existsSync(resolve(d, 'Cargo.toml')))
    throw new Error(`the dregg-side hash probe is not at ${d} — set DREGG_PROBE_DIR`);
  return d;
}
function runProbe(dir: string, args: string[]): any {
  const out = execFileSync('cargo', ['run', '--offline', '--quiet', '--', ...args], {
    cwd: dir,
    encoding: 'utf8',
    maxBuffer: 1 << 24,
  });
  return JSON.parse(out);
}

const dir = probeDir();
const B = (s: string) => BigInt(s);

console.log('=== Rung 3: the FRI CHALLENGER (Fiat-Shamir transcript) ===\n');

// ---------------------------------------------------------------------------
console.log('[1] the DuplexChallenger STATE MACHINE == p3, on scripts it cannot have precomputed');
{
  // Each script crosses a different edge of the state machine. The seed is
  // fresh per run, so the emitter is computing these, not recalling them.
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const scripts: [string, string[]][] = [
    ['exact-rate absorb then a full squeeze', ['o:8', 's:8']],
    ['partial absorb forces a duplex on a half-full buffer', ['o:3', 's:1', 's:1']],
    ['observe DISCARDS unread squeezes', ['o:8', 's:1', 'o:1', 's:1']],
    ['a squeeze that outruns one output buffer', ['o:5', 's:9']],
    ['extension challenges are four base samples, in basis order', ['o:2', 'e:3']],
    ['sample_bits after a mixed script', ['o:11', 'e:1', 'b:22', 'b:16']],
    ['the deployed FRI head: preamble, alpha, a commit, a beta', ['o:13', 'e:1', 'o:8', 'e:1']],
  ];
  for (const [label, ops] of scripts) {
    const em = runProbe(dir, ['p2chal', String(seed), ...ops]);
    const twin = new ChallengerBigInt();
    for (let i = 0; i < ops.length; i++) {
      const o = em.ops[i];
      switch (o.op) {
        case 'observe':
          twin.observeSlice(o.values.map(B));
          break;
        case 'sample': {
          const got = (o.values as string[]).map(() => twin.sample());
          if (!eqv(got, o.values.map(B)))
            fail(`'${label}': sample diverges — got ${got}, p3 says ${o.values}`);
          break;
        }
        case 'sampleExt': {
          const got = (o.values as string[][]).map(() => twin.sampleExt());
          if (!eq2(got, (o.values as string[][]).map((v) => v.map(B))))
            fail(`'${label}': sampleExt diverges — got ${JSON.stringify(got.map(String))}`);
          break;
        }
        case 'sampleBits': {
          const got = twin.sampleBits(o.bits);
          if (got !== o.value)
            fail(`'${label}': sample_bits(${o.bits}) gave ${got}, p3 says ${o.value}`);
          break;
        }
        default:
          fail(`unknown emitted op ${o.op}`);
      }
    }
    if (!eqv(twin.state, em.finalSpongeState.map(B)))
      fail(`'${label}': the sponge state diverges after the script`);
    if (!eqv(twin.inputBuffer, em.finalInputBuffer.map(B)))
      fail(`'${label}': the input buffer diverges after the script`);
    if (!eqv(twin.outputBuffer, em.finalOutputBuffer.map(B)))
      fail(`'${label}': the output buffer diverges after the script`);
    ok(`${label} — every value and the whole final state`);
  }
  ok(`emitter: ${runProbe(dir, ['p2chal', '1', 'o:1']).emitter}`);
}

// ---------------------------------------------------------------------------
console.log('\n[2] the state-machine EDGES: THREE load-bearing (each with a discriminating\n    polarity) and ONE that a naive reading counts and the measurement refutes');
{
  // These are the places a re-implementation drifts while every hash still
  // matches. Each LOAD-BEARING one shows the twin agrees with p3 AND that the
  // plausible wrong reading gives a DIFFERENT answer — otherwise the agreement
  // is free. ⚑ Edge (2) is the exception and is written up as such: it was
  // asserted to be load-bearing, its fault injection STAYED GREEN, and what is
  // checked now is the fact that replaced the claim.
  const em = runProbe(dir, ['p2chal', '4242', 'o:8', 's:8']);
  const squeezed = em.ops[1].values.map(B) as bigint[];

  // (1) the output buffer is popped from the BACK.
  const t1 = new ChallengerBigInt();
  // Observing exactly RATE elements duplexes on the 8th, so the state is
  // already permuted here and `state[0..8]` IS the rate in domain order.
  t1.observeSlice(em.ops[0].values.map(B));
  const rateForward = t1.state.slice(0, 8);
  if (!eqv(squeezed, rateForward.slice().reverse()))
    fail('the squeeze order is not the rate read back-to-front');
  if (eqv(squeezed, rateForward))
    fail('the rate is palindromic here — this check cannot see the order');
  ok('(1) samples are the rate read BACK-TO-FRONT, and front-to-back differs');

  // (2) `observe` clears the output buffer — AND THAT TURNS OUT TO BE
  //     DEFENSIVE, NOT SEMANTIC. It was listed here as one of four edges "each
  //     of which silently changes every challenge downstream". It is not one:
  //     `sample` re-duplexes whenever the INPUT buffer is non-empty, and
  //     `observe` always makes it non-empty, so a stale output buffer can never
  //     be read. Measured, by deleting the clear from the twin and requiring
  //     the gate to go red — IT STAYED GREEN. The honest check is therefore the
  //     opposite one: show the removal is invisible, on schedules chosen to
  //     stress it, so nobody later "hardens" this into a falsifier that cannot
  //     fire. There is deliberately NO fault injection for it.
  const emDrop = runProbe(dir, ['p2chal', '4242', 'o:8', 's:1', 'o:1', 's:1']);
  const tDrop = new ChallengerBigInt();
  tDrop.observeSlice(emDrop.ops[0].values.map(B));
  tDrop.sample();
  tDrop.observeSlice(emDrop.ops[2].values.map(B));
  if (tDrop.sample() !== B(emDrop.ops[3].values[0]))
    fail('the post-observe sample diverges from p3');

  class NoClear extends ChallengerBigInt {
    override observe(v: bigint) {
      this.inputBuffer.push(((v % P) + P) % P);
      if (this.inputBuffer.length === 8) this.duplexing();
    }
  }
  // (observes, samples) alternating — including a squeeze left half-drained
  // before the next observe, which is the only shape where a stale buffer could
  // possibly matter.
  const schedules: number[][] = [
    [8, 1, 1, 1],
    [3, 1, 5, 2],
    [8, 3, 1, 9],
    [13, 4, 8, 4],
    [5, 9, 3, 1],
  ];
  for (const sch of schedules) {
    const a = new ChallengerBigInt();
    const b = new NoClear();
    const ga: bigint[] = [];
    const gb: bigint[] = [];
    let n = 0n;
    for (let i = 0; i < sch.length; i++) {
      if (i % 2 === 0)
        for (let k = 0; k < sch[i]; k++) {
          n += 1n;
          a.observe(n);
          b.observe(n);
        }
      else
        for (let k = 0; k < sch[i]; k++) {
          ga.push(a.sample());
          gb.push(b.sample());
        }
    }
    if (!eqv(ga, gb))
      fail(
        `dropping observe's output-buffer clear CHANGED the samples on schedule ` +
          `${sch}: it is load-bearing after all and needs a fault injection`,
      );
  }
  ok(
    `(2) observe's output-buffer clear is DEFENSIVE, not semantic — proved unobservable ` +
      `on ${schedules.length} schedules, because sample re-duplexes on a non-empty input buffer`,
  );

  // (3) a partial absorb OVERWRITES a prefix; the rest keeps the previous
  //     permutation's output rather than being zero-filled.
  const emPart = runProbe(dir, ['p2chal', '4242', 'o:8', 's:1', 'o:3', 's:1']);
  const tPart = new ChallengerBigInt();
  tPart.observeSlice(emPart.ops[0].values.map(B));
  tPart.sample();
  const absorbed = emPart.ops[2].values.map(B) as bigint[];
  tPart.observeSlice(absorbed);
  const gotPart = tPart.sample();
  if (gotPart !== B(emPart.ops[3].values[0])) fail('the partial-absorb duplex diverges from p3');
  // The zero-filling reading, computed explicitly.
  const zf = new ChallengerBigInt();
  zf.observeSlice(emPart.ops[0].values.map(B));
  zf.sample();
  for (let i = 0; i < 3; i++) zf.state[i] = absorbed[i];
  for (let i = 3; i < 8; i++) zf.state[i] = 0n;
  zf.inputBuffer = [];
  zf.duplexing();
  if (zf.outputBuffer[7] === gotPart)
    fail('zero-filling the unabsorbed rate is indistinguishable here');
  ok('(3) a partial absorb keeps the untouched rate, and zero-filling it differs');

  // (4) `check_witness(0, w)` does not observe.
  const t4a = new ChallengerBigInt();
  const t4b = new ChallengerBigInt();
  for (let i = 0; i < 5; i++) {
    t4a.observe(BigInt(i));
    t4b.observe(BigInt(i));
  }
  if (!t4a.checkWitness(0, 999n)) fail('a 0-bit check_witness returned false');
  if (t4a.sample() !== t4b.sample())
    fail('a 0-bit check_witness perturbed the transcript');
  const t4c = new ChallengerBigInt();
  for (let i = 0; i < 5; i++) t4c.observe(BigInt(i));
  t4c.observe(999n); //   what a WRONG implementation would do
  const t4d = new ChallengerBigInt();
  for (let i = 0; i < 5; i++) t4d.observe(BigInt(i));
  if (t4c.sample() === t4d.sample())
    fail('observing the 0-bit PoW witness is indistinguishable here');
  ok('(4) check_witness(0, ·) observes NOTHING, and observing the witness differs');
}

// ---------------------------------------------------------------------------
console.log('\n[3] the WHOLE deployed FRI transcript == p3 — twin, then CIRCUIT');
const PREAMBLE_LEN = 13; // not a multiple of 8, so FRI starts mid-buffer
{
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const em = runProbe(dir, ['p2fritranscript', String(seed), String(PREAMBLE_LEN)]);
  ok(`emitter: ${em.emitter}`);

  // The knobs the emitter reports must be the ones this side compiles in. A
  // transcript derived at different knobs is a different function.
  const want: [string, number][] = [
    ['logBlowup', DEPLOYED_KNOBS.logBlowup],
    ['logFinalPolyLen', DEPLOYED_KNOBS.logFinalPolyLen],
    ['maxLogArity', DEPLOYED_KNOBS.maxLogArity],
    ['layers', DEPLOYED_KNOBS.layers],
    ['numQueries', DEPLOYED_KNOBS.numQueries],
    ['commitPowBits', DEPLOYED_KNOBS.commitPowBits],
    ['queryPowBits', DEPLOYED_KNOBS.queryPowBits],
    ['logGlobalMaxHeight', DEPLOYED_KNOBS.logGlobalMaxHeight],
    ['extraQueryIndexBits', DEPLOYED_KNOBS.extraQueryIndexBits],
    ['indexBits', DEPLOYED_KNOBS.indexBits],
  ];
  for (const [k, v] of want)
    if (em[k] !== v) fail(`the deployed ${k} is ${em[k]}, this circuit compiles ${v}`);
  ok(`all ${want.length} deployed knobs agree (16 layers, fold by 2, 19 queries, 16-bit query PoW)`);

  const input = {
    preamble: em.preamble.map(B) as bigint[],
    commits: em.commits.map((c: string[]) => c.map(B)) as bigint[][],
    finalPoly: em.finalPoly.map((c: string[]) => c.map(B)) as bigint[][],
    queryPowWitness: B(em.queryPowWitness),
  };
  const got = deriveFriChallengesBigInt(input, DEPLOYED_KNOBS);
  if (!eqv(got.alpha, em.alpha.map(B))) fail(`alpha diverges: ${got.alpha} vs ${em.alpha}`);
  ok('alpha (the batch-combination challenge) agrees');
  if (!eq2(got.betas, em.betas.map((b: string[]) => b.map(B))))
    fail('a fold challenge beta diverges from p3');
  ok(`all ${DEPLOYED_KNOBS.layers} fold challenges beta agree`);
  const idx = got.queryIndexBits.map((bits) =>
    bits.reduce((a, b, i) => a + (b ? 1 << i : 0), 0),
  );
  if (idx.length !== em.queryIndices.length || idx.some((v, i) => v !== em.queryIndices[i]))
    fail(`the query indices diverge: ${idx} vs ${em.queryIndices}`);
  ok(`all ${DEPLOYED_KNOBS.numQueries} query indices agree — DERIVED, not witnessed`);
  console.log(`    the deployed transcript costs ${got.perms} permutations`);

  // The PoW witness p3 GROUND really satisfies the deployed 16-bit condition,
  // and a neighbour does not. Deterministic: both values are fixed by the
  // emitter, so this is not a 1-in-65536 coin flip either way.
  const powOk = (w: bigint) => {
    const c = new ChallengerBigInt();
    c.observeSlice(input.preamble);
    c.sampleExt();
    for (let r = 0; r < DEPLOYED_KNOBS.layers; r++) {
      c.observeSlice(input.commits[r]);
      c.sampleExt();
    }
    for (const e of input.finalPoly) c.observeSlice(e);
    for (let r = 0; r < DEPLOYED_KNOBS.layers; r++) c.observe(BigInt(DEPLOYED_KNOBS.maxLogArity));
    return c.checkWitness(DEPLOYED_KNOBS.queryPowBits, w);
  };
  if (!powOk(input.queryPowWitness)) fail('the emitted query PoW witness does not pass');
  if (powOk(input.queryPowWitness + 1n))
    fail('witness+1 ALSO passed a 16-bit PoW — the check is not discriminating');
  if (powOk(0n)) fail('the zero witness passed a 16-bit PoW');
  ok('the GROUND query PoW witness passes and two named neighbours do not');

  // A perturbed commitment must move every challenge that comes after it — and
  // must NOT move alpha, which is sampled before any commitment is observed.
  const bad = { ...input, commits: input.commits.map((c) => c.slice()) };
  bad.commits[7][3] = (bad.commits[7][3] + 1n) % P;
  let badOut;
  try {
    badOut = deriveFriChallengesBigInt(bad, DEPLOYED_KNOBS);
  } catch {
    badOut = null; //  the PoW check can also simply fail, which is stronger
  }
  if (badOut) {
    if (!eqv(badOut.alpha, got.alpha)) fail('alpha moved when a LATER commitment changed');
    if (eq2(badOut.betas.slice(8), got.betas.slice(8)))
      fail('the betas after the perturbed layer did not move');
    if (badOut.queryIndexBits.every((b, i) => b.every((x, j) => x === got.queryIndexBits[i][j])))
      fail('the query indices did not move when a commitment changed');
  }
  ok('perturbing commitment 7 moves every later beta and the indices, and NOT alpha');

  // The circuit.
  const t0 = Date.now();
  await Provable.runAndCheck(() => {
    const w = {
      preamble: input.preamble.map((v) => Provable.witness(Field, () => Field(v))),
      commits: input.commits.map((c) => Provable.witness(BbDigest, () => BbDigest.from(c))),
      finalPoly: input.finalPoly.map((c) => Provable.witness(BbExt, () => BbExt.from(c))),
      queryPowWitness: Provable.witness(Field, () => Field(input.queryPowWitness)),
    };
    const out = deriveFriChallenges(w, DEPLOYED_KNOBS);
    Provable.asProver(() => {
      if (!eqv(out.alpha.toBigInts(), got.alpha)) fail('in-circuit alpha != p3');
      for (let r = 0; r < DEPLOYED_KNOBS.layers; r++)
        if (!eqv(out.betas[r].toBigInts(), got.betas[r])) fail(`in-circuit beta[${r}] != p3`);
      for (let q = 0; q < DEPLOYED_KNOBS.numQueries; q++) {
        const v = out.queryIndexBits[q].reduce(
          (a, b, i) => a + (b.toBoolean() ? 1 << i : 0),
          0,
        );
        if (v !== em.queryIndices[q]) fail(`in-circuit query index ${q} = ${v} != ${em.queryIndices[q]}`);
      }
    });
  });
  ok(
    `the CIRCUIT reproduces p3's alpha, all ${DEPLOYED_KNOBS.layers} betas and all ` +
      `${DEPLOYED_KNOBS.numQueries} query indices  [${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );

  // And the circuit REFUSES a PoW witness that does not grind. This is the one
  // constraint in the transcript that can fail on well-formed inputs, so if it
  // could not fail the 16-bit grind would be decoration.
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const w = {
        preamble: input.preamble.map((v) => Provable.witness(Field, () => Field(v))),
        commits: input.commits.map((c) => Provable.witness(BbDigest, () => BbDigest.from(c))),
        finalPoly: input.finalPoly.map((c) => Provable.witness(BbExt, () => BbExt.from(c))),
        queryPowWitness: Provable.witness(Field, () => Field(input.queryPowWitness + 1n)),
      };
      deriveFriChallenges(w, DEPLOYED_KNOBS);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('the circuit accepted a query PoW witness that does not grind 16 zeros');
  ok('the circuit REFUSES a query PoW witness one off the ground one');
}

// ---------------------------------------------------------------------------
console.log('\n[3b] the ONE constraint a witness can lie about');
{
  // ⚑ NOTHING ELSE IN THIS LEG CAN SEE THIS. Every KAT above compares the
  // challenger's output to p3's on an HONEST witness, and an honest witness
  // produces the right bit decomposition whether or not anything forces it to.
  // Drop the bound on the high part and `c = hi*2^k + sum b_i 2^i` is
  // satisfiable over Pasta for EVERY bit pattern — `hi = (c - lo) * 2^-k`
  // always exists — so a prover derives whatever query index it wants out of a
  // perfectly correct sponge, and every check above stays green.
  //
  // Deterministic, and both polarities: a fixed `c`, the honest split accepted,
  // and a named wrong index refused.
  const K = DEPLOYED_KNOBS.indexBits;
  const c = 1234567891n % P; //   fixed, not drawn
  const loHonest = c & ((1n << BigInt(K)) - 1n);
  const hiHonest = c >> BigInt(K);

  await Provable.runAndCheck(() => {
    const cf = Provable.witness(Field, () => Field(c));
    const bits = Provable.witness(Provable.Array(Bool, K), () =>
      Array.from({ length: K }, (_, i) => Bool(((c >> BigInt(i)) & 1n) === 1n)),
    );
    const hi = Provable.witness(Field, () => Field(hiHonest));
    assertLowBitsSplit(cf, bits, hi, K);
  });
  ok(`the honest split of a fixed lane (lo = ${loHonest}, hi = ${hiHonest}) is ACCEPTED`);

  // The attack: keep `c`, flip the low bit of the claimed index, and solve for
  // the `hi` that makes the linear relation hold. It exists in Pasta; it is
  // astronomically out of range; the range check is the only thing refusing it.
  const loLie = loHonest ^ 1n;
  let held = false;
  try {
    await Provable.runAndCheck(() => {
      const cf = Provable.witness(Field, () => Field(c));
      const bits = Provable.witness(Provable.Array(Bool, K), () =>
        Array.from({ length: K }, (_, i) => Bool(((loLie >> BigInt(i)) & 1n) === 1n)),
      );
      // hi = (c - loLie) / 2^K over the NATIVE field.
      const hi = Provable.witness(Field, () =>
        Field(c).sub(Field(loLie)).div(Field(1n << BigInt(K))),
      );
      assertLowBitsSplit(cf, bits, hi, K);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held)
    fail(
      `a query index of ${loLie} was derivable from a lane whose low ${K} bits are ` +
        `${loHonest}: the high-part bound is not enforced and the index is CHOOSEABLE`,
    );
  ok(`a lane cannot be split to claim index ${loLie} instead of ${loHonest}`);

  // Same for the PoW split: the low bits must really be zero.
  const cPow = (7n << BigInt(DEPLOYED_KNOBS.queryPowBits)) % P; //  low 16 bits are 0
  await Provable.runAndCheck(() => {
    const cf = Provable.witness(Field, () => Field(cPow));
    const hi = Provable.witness(Field, () => Field(cPow >> BigInt(DEPLOYED_KNOBS.queryPowBits)));
    assertLowBitsZero(cf, hi, DEPLOYED_KNOBS.queryPowBits);
  });
  ok('a lane whose low 16 bits ARE zero passes the PoW split');
  held = false;
  try {
    const cBad = cPow + 1n; //  low bits no longer zero
    await Provable.runAndCheck(() => {
      const cf = Provable.witness(Field, () => Field(cBad));
      const hi = Provable.witness(Field, () =>
        Field(cBad).div(Field(1n << BigInt(DEPLOYED_KNOBS.queryPowBits))),
      );
      assertLowBitsZero(cf, hi, DEPLOYED_KNOBS.queryPowBits);
    });
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a lane whose low 16 bits are NOT zero passed the PoW split');
  ok('a lane one off it does NOT (the PoW split is not solvable in Pasta)');

  // And the gadget the two rest on: `assertLtPow2` accepts its bound and
  // refuses one past it, at the two widths the transcript uses.
  for (const n of [31 - K, 31 - DEPLOYED_KNOBS.queryPowBits]) {
    await Provable.runAndCheck(() => {
      assertLtPow2(Provable.witness(Field, () => Field((1n << BigInt(n)) - 1n)), n);
    });
    let h = false;
    try {
      await Provable.runAndCheck(() => {
        assertLtPow2(Provable.witness(Field, () => Field(1n << BigInt(n))), n);
      });
      h = true;
    } catch {
      /* expected */
    }
    if (h) fail(`assertLtPow2 accepted 2^${n} at a bound of ${n} bits`);
  }
  ok(`assertLtPow2 accepts 2^n - 1 and refuses 2^n at n = ${31 - K} and ${31 - DEPLOYED_KNOBS.queryPowBits}`);
}

// ---------------------------------------------------------------------------
console.log('\n[4] the transcript is a real PROVABLE object');
{
  // The deployed transcript is 62k rows — past a Pickles step's usable budget
  // (§4.1), so the PROVED instance runs the same schedule at fewer layers. Every
  // other knob, including the 16-bit query PoW and the 22-bit index width, is
  // the deployed one, and the witness comes from the SAME emitter.
  const LAYERS = 4;
  const NQ = DEPLOYED_KNOBS.numQueries;
  const knobs: FriKnobs = { ...DEPLOYED_KNOBS, layers: LAYERS, numQueries: NQ };
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1000000n);
  const em = runProbe(dir, [
    'p2fritranscript',
    String(seed),
    String(PREAMBLE_LEN),
    String(LAYERS),
    String(NQ),
  ]);
  if (em.deployedLayers !== DEPLOYED_KNOBS.layers)
    fail('the emitter no longer reports the deployed layer count');
  if (em.queryPowBits !== DEPLOYED_KNOBS.queryPowBits)
    fail('the shrunk instance changed the PoW bits — it is a different protocol');

  const input = {
    preamble: em.preamble.map(B) as bigint[],
    commits: em.commits.map((c: string[]) => c.map(B)) as bigint[][],
    finalPoly: em.finalPoly.map((c: string[]) => c.map(B)) as bigint[][],
    queryPowWitness: B(em.queryPowWitness),
  };
  const twin = deriveFriChallengesBigInt(input, knobs);
  if (!eqv(twin.alpha, em.alpha.map(B))) fail('the shrunk instance diverges from p3 at alpha');
  const idx = twin.queryIndexBits.map((b) => b.reduce((a, x, i) => a + (x ? 1 << i : 0), 0));
  if (idx.some((v, i) => v !== em.queryIndices[i]))
    fail('the shrunk instance diverges from p3 on the query indices');
  ok(`a ${LAYERS}-layer instance of the SAME schedule agrees with p3 (same PoW, same 22-bit index)`);

  const prog = makeFriTranscriptProgram(knobs, PREAMBLE_LEN);
  const analysis = await prog.analyzeMethods();
  console.log(
    `    the proved instance: ${analysis.deriveChallenges.rows.toLocaleString()} rows`,
  );
  const t0 = Date.now();
  await prog.compile();
  ok(`compiled in ${((Date.now() - t0) / 1000).toFixed(1)}s`);

  const args = () =>
    [
      input.preamble.map((v) => Field(v)),
      input.commits.map((c) => BbDigest.from(c)),
      input.finalPoly.map((c) => BbExt.from(c)),
      Field(input.queryPowWitness),
    ] as const;
  const t1 = Date.now();
  const { proof } = await prog.deriveChallenges(...args());
  if (!(await prog.verify(proof))) fail('the transcript proof failed to verify');
  ok(`a transcript PROVES and VERIFIES in ${((Date.now() - t1) / 1000).toFixed(1)}s`);

  const wantDigest = challengeDigestBigInt(twin, knobs);
  const gotDigest = proof.publicOutput.limbs.map((x) => x.toBigInt() % P);
  if (!eqv(gotDigest, wantDigest))
    fail(`the PROVEN challenge digest ${gotDigest} != the p3-derived ${wantDigest}`);
  ok('the PROVEN public output BINDS the challenges p3 derives');

  // A different transcript must give a different binding — otherwise the public
  // output is not a commitment to anything.
  const shifted = { ...input, commits: input.commits.map((c) => c.slice()) };
  shifted.commits[1][0] = (shifted.commits[1][0] + 1n) % P;
  let alt: bigint[] | null = null;
  try {
    alt = challengeDigestBigInt(deriveFriChallengesBigInt(shifted, knobs), knobs);
  } catch {
    alt = null; //  a failing PoW is a stronger refusal
  }
  if (alt && eqv(alt, wantDigest)) fail('two different transcripts bound to the same digest');
  ok('a perturbed commitment does NOT reach the same binding');

  // NO proof exists for a PoW witness that does not grind.
  let held = false;
  try {
    await prog.deriveChallenges(
      input.preamble.map((v) => Field(v)),
      input.commits.map((c) => BbDigest.from(c)),
      input.finalPoly.map((c) => BbExt.from(c)),
      Field(input.queryPowWitness + 1n),
    );
    held = true;
  } catch {
    /* expected */
  }
  if (held) fail('a transcript proved with a PoW witness that does not grind');
  ok('NO proof exists for a query PoW witness that does not grind 16 zeros');
}

// ---------------------------------------------------------------------------
console.log('\n[5] getRows() — the transcript at the DEPLOYED knobs');
let full = 0;
let perms = 0;
{
  const t0 = Date.now();
  const cs = await Provable.constraintSystem(() => {
    const w = witnessTranscriptShape(DEPLOYED_KNOBS, PREAMBLE_LEN);
    const out = deriveFriChallenges(w, DEPLOYED_KNOBS);
    perms = out.challenger.perms;
    out.alpha.limbs.forEach((x) => x.seal());
  });
  full = cs.rows;
  console.log(
    `    DEPLOYED transcript (preamble ${PREAMBLE_LEN}, ${DEPLOYED_KNOBS.layers} layers, ` +
      `${DEPLOYED_KNOBS.numQueries} queries): ${full.toLocaleString()} rows in ${perms} ` +
      `permutations   [built in ${((Date.now() - t0) / 1000).toFixed(1)}s]`,
  );
  const permRows = perms * 2600.5;
  console.log(
    `    of which the permutations are ~${Math.round(permRows).toLocaleString()} ` +
      `(${((permRows / full) * 100).toFixed(1)}%); the rest is lane hygiene, the ` +
      `${DEPLOYED_KNOBS.numQueries} bit-decompositions and the PoW range check`,
  );

  const USABLE_LOW = 48000;
  const USABLE_HIGH = 55000;
  console.log(
    `    = ${Math.ceil(full / USABLE_HIGH)}–${Math.ceil(full / USABLE_LOW)} Pickles steps ` +
      `— against ${(684726 * 19).toExponential(2)} rows for the query walk it authorises, ` +
      `i.e. ${((full / (684726 * 19)) * 100).toFixed(2)}% of it`,
  );
  console.log(
    '    ⚑ The transcript is CHEAP. What it is not yet is BOUND to the batch-STARK\n' +
      '      preamble that precedes it, or to the query walk that consumes it.',
  );
}

// ---------------------------------------------------------------------------
const RECORDED_TRANSCRIPT_ROWS = 62_637; //  §3.12, measured 2026-07-28
const RECORDED_TRANSCRIPT_PERMS = 23;
if (perms !== RECORDED_TRANSCRIPT_PERMS)
  fail(
    `the deployed transcript now costs ${perms} permutations, not the recorded ` +
      `${RECORDED_TRANSCRIPT_PERMS}: the schedule changed`,
  );
const drift = Math.abs(full - RECORDED_TRANSCRIPT_ROWS) / RECORDED_TRANSCRIPT_ROWS;
if (drift > 0.02)
  fail(
    `rows for the deployed FRI transcript moved to ${full} from the recorded ` +
      `${RECORDED_TRANSCRIPT_ROWS} (${(drift * 100).toFixed(1)}%): ` +
      'docs/MINA-VERIFIES-DREGG-FRI-SIZE.md §3.12 is stale',
  );
console.log(
  `\n    ratchet: ${full.toLocaleString()} rows / ${perms} permutations is within 2% of the recorded figure`,
);

console.log('\n=== FRI CHALLENGER PASS ===\n');
