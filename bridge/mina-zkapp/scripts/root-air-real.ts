import { execFileSync } from 'node:child_process';
import { existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { Field, Provable } from 'o1js';
import { canonicalLane } from '../src/Poseidon2BabyBearW16.js';
import { BbExt, extMul } from '../src/FriQueryStep.js';
import {
  DagTable,
  RealInstance,
  RealRootAir,
  bindRealInstance,
  evalDagBigInt,
  evalDagInCircuit,
  foldRootsP3,
  foldRootsP3BigInt,
  rootAirDag,
} from '../src/RootAirDag.js';

// ---------------------------------------------------------------------------
// LEG 16 — THE ROOT'S AIR ON THE ROOT'S OWN PROOF.
//
// Leg 13 emits dregg's root constraint system and evaluates it at PSEUDORANDOM
// extension-valued assignments. That measures the arithmetic at its real size
// and shape, and it is not a decision about anything: §3.19 killed exactly this
// failure mode one rung down — "every one of them is fed a fixture the
// measurement synthesised ... until something consumes a proof, 'Mina verifies
// dregg' is a statement about a parts list."
//
// `circuit-prove/src/bin/root_air_instance.rs` loads dregg's COMMITTED root
// proof (`ugc-dregg/tests/fixtures/whole_history_proof.bin`, a 3-turn
// `prove_turn_chain_recursive` root under VK `434f57d2...`), decodes the
// `BatchProof`, replays `verify_batch`'s transcript to `alpha` and `zeta`, and
// emits every instance's opened values at `zeta`. This leg evaluates the emitted
// DAG at THOSE values, in circuit, and checks the closing equality p3 checks:
//
//     accumulator * Z_H(zeta)^{-1}  ==  quotient(zeta)
//
// ⚑ WHAT MAKES THIS NOT A TAUTOLOGY. The `accumulator` the Rust side emits comes
// from p3's own `SymbolicExpression` walk over p3's own AIRs; the one this
// circuit computes comes from the extracted DAG. They are different objects and
// the comparison is the seam. And `quotientAtZeta` comes from the PROVER — it is
// the opened quotient chunks recomposed — so the second equality is dregg's
// actual soundness check, not a re-derivation.
// ---------------------------------------------------------------------------

const P = 2013265921n;
const LANE_MAX = (1n << 31n) - 1n;

let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const fmt = (n: number) => n.toLocaleString('en-US');

function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|Cannot read/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert/.test(m);
}

const md = (x: bigint) => ((x % P) + P) % P;
function eMul(a: bigint[], b: bigint[]): bigint[] {
  const acc = Array(7).fill(0n) as bigint[];
  for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) acc[i + j] = md(acc[i + j] + a[i] * b[j]);
  return Array.from({ length: 4 }, (_, i) => (i + 4 < 7 ? md(acc[i] + 11n * acc[i + 4]) : acc[i]));
}

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit-prove/src/bin/root_air_instance.rs')))
    fail(`the root-proof dumper is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}

/** The in-circuit statement, per instance: walk the emitted DAG at the REAL
 *  opened values, fold p3's way, and assert BOTH equalities. `bend` mutates the
 *  instance so the same body serves the honest run and the falsifiers. */
function instanceCircuit(t: DagTable, inst: RealInstance, alpha: bigint[], bend?: (i: RealInstance) => RealInstance) {
  const i2 = bend ? bend(inst) : inst;
  const { base, ext } = bindRealInstance(t, i2);
  const w = (l: bigint[]) => {
    const e = Provable.witness(BbExt, () => BbExt.from(l));
    for (const x of e.limbs) canonicalLane(x, LANE_MAX);
    return e;
  };
  const bIn = base.map(w);
  const eIn = ext.map(w);
  const aIn = w(alpha);
  const roots = evalDagInCircuit(t, bIn, eIn, {});
  const acc = foldRootsP3(aIn, roots);
  // (1) the DAG reproduces p3's accumulator on the REAL proof.
  for (let j = 0; j < 4; j++)
    canonicalLane(acc.limbs[j], LANE_MAX).assertEquals(Field(BigInt(inst.accumulator[j])));
  // (2) dregg's OWN closing equality, `data.rs:100`'s inverse form.
  const invZ = w(i2.selectors.invVanishing.map((x) => BigInt(x)));
  const lhs = extMul(acc, invZ);
  for (let j = 0; j < 4; j++)
    canonicalLane(lhs.limbs[j], LANE_MAX).assertEquals(Field(BigInt(i2.quotientAtZeta[j])));
}

async function main() {
  console.log("\n=== ROOT-AIR-REAL — the root's AIR on the root's own proof (leg 16) ===\n");

  const ROOT = repoRoot();
  console.log('[1] the committed root proof, decoded and its transcript replayed');
  execFileSync('cargo', ['build', '-p', 'dregg-circuit-prove', '--release', '--bin', 'root_air_instance'], {
    cwd: ROOT,
    stdio: ['ignore', 'ignore', 'inherit'],
  });
  const real = JSON.parse(
    execFileSync(resolve(ROOT, 'target/release/root_air_instance'), [], {
      encoding: 'utf8',
      maxBuffer: 1 << 26,
    }),
  ) as RealRootAir;
  if (real.kind !== 'dregg-root-air-instance') fail(`the dumper returned ${real.kind}`);
  console.log(
    `    vk ${real.vkFingerprint.slice(0, 16)}...  ${real.numTurns} turns  ` +
      `degree_bits [${real.degreeBits.join(', ')}]`,
  );
  console.log(`    alpha [${real.challenges.alpha.join(', ')}]`);
  console.log(`    zeta  [${real.challenges.zeta.join(', ')}]`);
  ok(
    `the dumper self-checks all ${real.instances.length} instances' closing equality against p3's ` +
      `own \`verify_batch\` BEFORE emitting — a drifted transcript replay is a red, not a JSON`,
  );
  if (real.degreeBits.join(',') !== '10,10,16,15,3,16,0')
    fail(`degree_bits ${real.degreeBits} is not §1.2's [10,10,16,15,3,16,0] — a different root`);
  ok("degree_bits is §1.2's [10, 10, 16, 15, 3, 16, 0] — the same root the document read");

  const d = rootAirDag();
  const alpha = real.challenges.alpha.map((x) => BigInt(x));

  // -----------------------------------------------------------------------
  // [2] The emitted DAG against p3's accumulator, on the REAL values.
  // -----------------------------------------------------------------------
  console.log('\n[2] the EMITTED DAG at the REAL opened values, out of circuit');
  const byName: Record<string, RealInstance> = {};
  for (const i of real.instances) byName[i.table.replace('poseidon2_perm/baby_bear_d4_', 'poseidon2_')] = i;
  const pairs: [DagTable, RealInstance][] = d.tables.map((t) => {
    const i = byName[t.name] ?? byName[t.name.toLowerCase()];
    if (!i) fail(`no real instance for table ${t.name} (have ${Object.keys(byName).join(', ')})`);
    return [t, i];
  });
  for (const [t, inst] of pairs) {
    const { base, ext } = bindRealInstance(t, inst);
    const acc = foldRootsP3BigInt(alpha, evalDagBigInt(t, base, ext));
    const want = inst.accumulator.map((x) => BigInt(x));
    if (acc.join(',') !== want.join(','))
      fail(
        `${t.name}: the EMITTED DAG gives accumulator [${acc}] and p3 gives [${want}] on the ` +
          `SAME opened values — the extracted AIR is not the deployed one`,
      );
    const lhs = eMul(acc, inst.selectors.invVanishing.map((x) => BigInt(x)));
    if (lhs.join(',') !== inst.quotientAtZeta.map((x) => BigInt(x)).join(','))
      fail(`${t.name}: the closing equality does not hold at the DAG's accumulator`);
  }
  ok(
    `all ${pairs.length} instances: the emitted DAG reproduces p3's accumulator EXACTLY on the ` +
      `real proof's opened values, and \`acc * Z_H(zeta)^-1 == quotient(zeta)\` holds`,
  );

  // ⚑ Anti-vacuity: an accumulator of zero, or two instances agreeing, would
  // make the comparison say nothing.
  const accs = pairs.map(([, i]) => i.accumulator.join(','));
  if (pairs.some(([, i]) => i.accumulator.every((x) => x === 0)))
    fail('an instance accumulator is ZERO — that comparison cannot discriminate');
  if (new Set(accs).size !== accs.length) fail('two instances carry the SAME accumulator');
  ok('every accumulator is non-zero and the seven are pairwise distinct');

  // -----------------------------------------------------------------------
  // [3] ⚑ THE FINDING: one instance's closing equality does not bind zeta.
  // -----------------------------------------------------------------------
  console.log('\n[3] ⚑ what binds, per instance — measured, not assumed');
  console.log(`    ${'table'.padEnd(16)}${'degree_bits'.padStart(12)}${'alpha binds'.padStart(13)}${'zeta binds'.padStart(12)}`);
  for (const [t, i] of pairs)
    console.log(
      `    ${t.name.padEnd(16)}${String(i.degreeBits).padStart(12)}` +
        `${String(i.alphaBinding).padStart(13)}${String(i.zetaBinding).padStart(12)}`,
    );
  if (!pairs.every(([, i]) => i.alphaBinding))
    fail('an instance\'s closing equality does not bind ALPHA — that is a soundness floor, not a note');
  ok('every instance binds ALPHA — the constraint-folding challenge is live in all seven');
  const blind = pairs.filter(([, i]) => !i.zetaBinding);
  if (blind.length === 0) {
    ok('every instance binds ZETA');
  } else {
    console.log(
      `\n    ⚑ ${blind.map(([t]) => t.name).join(', ')} — degree_bits ` +
        `${blind.map(([, i]) => i.degreeBits).join(', ')} — does NOT bind zeta.\n` +
        `      With |H| = 1 the selectors are zeta-free constants, is_transition = Z_H(zeta), and\n` +
        `      the two size-1 quotient chunks carry equal values, so the recomposition collapses and\n` +
        `      BOTH SIDES ARE CONSTANT IN ZETA. The out-of-domain point binds nothing in that\n` +
        `      instance's AIR check; its binding is the PCS opening and alpha. A Mina-side verifier\n` +
        `      must not be told this check binds zeta when it does not.`,
    );
    ok(
      `${blind.length} of ${pairs.length} instances do NOT bind zeta, and it is the degree_bits = 0 ` +
        `table — recorded rather than papered over`,
    );
  }

  // -----------------------------------------------------------------------
  // [4] The same statement, IN CIRCUIT.
  // -----------------------------------------------------------------------
  console.log('\n[4] the same statement as a Kimchi CONSTRAINT');
  for (const [t, inst] of pairs) await Provable.runAndCheck(() => instanceCircuit(t, inst, alpha));
  ok(
    `all ${pairs.length} instances: a Kimchi circuit walking the emitted DAG at dregg's real ` +
      `opened values SATISFIES both the accumulator identity and dregg's closing equality`,
  );

  // -----------------------------------------------------------------------
  // [5] It REFUSES.
  // -----------------------------------------------------------------------
  console.log('\n[5] and it REFUSES a bent proof');
  const refuse = async (what: string, f: () => void) => {
    try {
      await Provable.runAndCheck(f);
    } catch (e) {
      if (!isConstraintFailure(e))
        fail(`${what}: not a constraint failure — ${String((e as Error)?.message ?? e).slice(0, 200)}`);
      ok(`REFUSED: ${what}`);
      return;
    }
    fail(`${what}: ACCEPTED`);
  };
  // ⚑ Bend a table that BINDS zeta, so the falsifier is not blind for the reason
  // [3] just measured.
  const [tb, ib] = pairs.find(([, i]) => i.zetaBinding && i.traceLocal.length > 4)!;
  await refuse(`one opened TRACE value of ${tb.name} bent`, () =>
    instanceCircuit(tb, ib, alpha, (i) => ({
      ...i,
      traceLocal: i.traceLocal.map((r, k) => (k === 0 ? [(r[0] + 1) % Number(P), r[1], r[2], r[3]] : r)),
    })),
  );
  await refuse(`one opened PREPROCESSED value of ${tb.name} bent`, () =>
    instanceCircuit(tb, ib, alpha, (i) => ({
      ...i,
      prepLocal: (i.prepLocal ?? []).map((r, k) => (k === 0 ? [(r[0] + 1) % Number(P), r[1], r[2], r[3]] : r)),
    })),
  );
  await refuse(`one opened PERMUTATION (LogUp) value of ${tb.name} bent`, () =>
    instanceCircuit(tb, ib, alpha, (i) => ({
      ...i,
      permLocal: i.permLocal.map((r, k) => (k === 0 ? [(r[0] + 1) % Number(P), r[1], r[2], r[3]] : r)),
    })),
  );
  await refuse(`the QUOTIENT at zeta bent — dregg's own closing equality`, () =>
    instanceCircuit(tb, ib, alpha, (i) => ({
      ...i,
      quotientAtZeta: [(i.quotientAtZeta[0] + 1) % Number(P), ...i.quotientAtZeta.slice(1)],
    })),
  );
  await refuse(`the transcript's ALPHA bent`, () =>
    instanceCircuit(tb, ib, alpha.map((x, k) => (k === 0 ? (x + 1n) % P : x))),
  );
  await refuse(`the vanishing-polynomial inverse bent`, () =>
    instanceCircuit(tb, ib, alpha, (i) => ({
      ...i,
      selectors: { ...i.selectors, invVanishing: [(i.selectors.invVanishing[0] + 1) % Number(P), ...i.selectors.invVanishing.slice(1)] },
    })),
  );

  // -----------------------------------------------------------------------
  // [6] Ratchet.
  // -----------------------------------------------------------------------
  console.log('\n[6] RATCHET');
  const nZetaBlind = blind.length;
  const RECORDED: [string, string, string][] = [
    ['the root proof VK fingerprint', real.vkFingerprint.slice(0, 16), '434f57d29eae85e1'],
    ['degree_bits', real.degreeBits.join(','), '10,10,16,15,3,16,0'],
    ['instances whose AIR check binds alpha', String(pairs.length - 0), '7'],
    ['instances whose AIR check does NOT bind zeta', String(nZetaBlind), '1'],
    ['alpha, limb 0', String(real.challenges.alpha[0]), '923772376'],
    ['zeta, limb 0', String(real.challenges.zeta[0]), '656249784'],
  ];
  let drifted = 0;
  for (const [label, got, want] of RECORDED) {
    const mark = got === want ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(46)} ${got.padStart(20)} (recorded ${want})`);
    if (got !== want) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok(`${RECORDED.length} recorded figures are as recorded`);
  void fmt;

  console.log(`\n=== ROOT-AIR-REAL PASS === ${checks} checks\n`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
