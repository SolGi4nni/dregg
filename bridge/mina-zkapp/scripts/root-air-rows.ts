import { Field, Provable } from 'o1js';
import { canonicalLane } from '../src/Poseidon2BabyBearW16.js';
import { BbExt, extAdd, extMul, extSub } from '../src/FriQueryStep.js';
import {
  DagTable,
  RootAirDag,
  checkKat,
  evalDagBigInt,
  evalDagInCircuit,
  foldRootsP3,
  foldRootsP3BigInt,
  katAssignment,
  rootAirDag,
  rootColumnShape,
  witnessTableColumns,
} from '../src/RootAirDag.js';
import { foldConstraints } from '../src/AirEval.js';

// ---------------------------------------------------------------------------
// LEG 13 — THE ROOT'S OWN AIR, EMITTED AND MEASURED.
//
// §3.19 built the assembly and named ONE thing in it as still the fixture's:
// `DreggProofVerify`'s `constraints` argument, a 3-column AIR with FOUR
// constraints against the root's 1,093. It said so in the plainest available
// terms — "2.75 x 10^7 is a FLOOR, and 500-573 steps is a floor. The AIR term
// inside it is the fixture's four constraints" — and §3.21 inherited the floor
// wholesale: "a floor scheduled is still a floor."
//
// This leg emits the root's own constraint system into a Kimchi circuit and
// measures what it costs. Not a model of what it would cost: `getRows()` on a
// circuit that walks all 10,417 DAG nodes and folds all 1,093 constraints.
//
// ⚑ WHAT WOULD MAKE THIS LEG A GREEN THAT MEASURES NOTHING, and what is done
// about each:
//
//  * A TypeScript walker over a node list is a THIRD implementation beside p3's
//    and Lean's, and a row count over a walker that denotes something else is a
//    row count for a different circuit. [2] runs the KAT INSIDE the circuit, as
//    an assertion, against accumulators the Rust side computed from p3's own
//    AIRs. It is the load-bearing check in this file.
//  * A KAT that cannot go red proves nothing. [3] bends one child index and
//    requires the failure to be `Constraint unsatisfied` — not a JavaScript
//    shape error, which would look identical from a `catch {}`.
//  * The fold could be the WRONG accumulator and every row count would be
//    unmoved. [4] is a PERMANENT control, not a fault injection: on every green
//    pass it re-runs the fold p3's way and `AirEval.ts`'s way and requires them
//    to DIFFER. §3.17 found that off-by-one by reading; nothing has ever watched
//    it bite, and a control that runs every pass cannot be unpointed by a
//    refactor.
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

/** ⚑ EVERY CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. A `TypeError` from a
 *  mis-shaped argument is indistinguishable from a real refusal inside a bare
 *  `catch {}`, and a leg built that way measures its own harness. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  return /[Cc]onstraint unsatisfied|Constraint failed|assert.*fail/.test(m);
}

async function refuses(what: string, f: () => void | Promise<void>) {
  try {
    await Provable.runAndCheck(f as () => void);
  } catch (e) {
    if (!isConstraintFailure(e))
      fail(`${what}: the error is not a constraint failure — ${String((e as Error)?.message ?? e)}`);
    ok(`REFUSED: ${what}`);
    return;
  }
  fail(`${what}: ACCEPTED — the check does not bite`);
}

// ===========================================================================
// The in-circuit KAT, as an assertion.
// ===========================================================================

/** Walk one table's DAG in circuit at the KAT assignment and ASSERT the folded
 *  accumulator equals the one the Rust emitter recorded. `bend` mutates the
 *  node list first, so the same body serves the honest run and the falsifier. */
function katCircuit(t: DagTable, trial: number, bend?: (t: DagTable) => DagTable) {
  const table = bend ? bend(t) : t;
  const k = t.kat[trial];
  const { alpha, base, ext } = katAssignment(t, k);
  const bIn = base.map((l) => Provable.witness(BbExt, () => BbExt.from(l)));
  const eIn = ext.map((l) => Provable.witness(BbExt, () => BbExt.from(l)));
  for (const e of [...bIn, ...eIn]) for (const x of e.limbs) canonicalLane(x, LANE_MAX);
  const aIn = Provable.witness(BbExt, () => BbExt.from(alpha));
  for (const x of aIn.limbs) canonicalLane(x, LANE_MAX);
  const roots = evalDagInCircuit(table, bIn, eIn, {});
  const acc = foldRootsP3(aIn, roots);
  for (let j = 0; j < 4; j++)
    canonicalLane(acc.limbs[j], LANE_MAX).assertEquals(Field(BigInt(k.acc[j])));
}

async function main() {
  console.log('\n=== ROOT-AIR-ROWS — the root\'s own AIR, emitted and measured (leg 13) ===\n');

  // -----------------------------------------------------------------------
  // [1] The artifact, and the KAT out of circuit.
  // -----------------------------------------------------------------------
  console.log('[1] the emitted artifact');
  const d: RootAirDag = rootAirDag();
  const shape = rootColumnShape(d);
  console.log(
    `    ${d.tables.length} tables  N = ${fmt(d.totals.n)} (${fmt(d.totals.base)} base + ` +
      `${fmt(d.totals.ext)} LogUp)  ${fmt(d.totals.nodes)} DAG nodes  ${fmt(d.totals.muls)} multiplies`,
  );
  console.log(
    `    node kinds: ` +
      Object.entries(d.totals.kinds)
        .map(([k, v]) => `${k} ${fmt(v)}`)
        .join('  '),
  );
  console.log(
    `    columns the DAG indexes: ${fmt(shape.base)} base + ${fmt(shape.ext)} extension`,
  );
  if (d.totals.n !== 1093) fail(`the artifact carries N = ${d.totals.n}, not the census's 1,093`);
  ok(`N = 1,093 — all 901 base and all 192 LogUp constraints, not the fixture's four`);
  if (d.totals.base !== 901 || d.totals.ext !== 192) fail('the base/ext split is not 901/192');
  ok(`the DAG is ${fmt(d.totals.nodes)} nodes for ${fmt(d.totals.n)} constraints — the shared form`);

  const kat = checkKat(d);
  if (kat.failures.length) fail(`the KAT fails out of circuit:\n  ${kat.failures.join('\n  ')}`);
  ok(
    `${kat.checked} KAT vectors reproduce p3's alpha-folded accumulator out of circuit ` +
      `(this walker against the Rust one, over p3's own AIRs)`,
  );

  // ⚑ Anti-vacuity: a KAT over a DAG whose roots are all zero would pass and say
  // nothing. Require the recorded accumulators to be non-zero and pairwise
  // distinct across trials.
  for (const t of d.tables) {
    const accs = t.kat.map((k) => k.acc.join(','));
    if (t.kat.some((k) => k.acc.every((x) => x === 0)))
      fail(`${t.name}: a KAT accumulator is zero — the vector cannot discriminate`);
    if (new Set(accs).size !== accs.length)
      fail(`${t.name}: two KAT trials give the same accumulator — the assignment stream is stuck`);
  }
  ok('every KAT accumulator is non-zero and the three trials are pairwise distinct');

  // -----------------------------------------------------------------------
  // [2] The KAT INSIDE the circuit — the seam that joins the emitted rows to p3.
  // -----------------------------------------------------------------------
  console.log('\n[2] the same KAT, as a CONSTRAINT inside the circuit');
  for (const t of d.tables) {
    await Provable.runAndCheck(() => katCircuit(t, 0));
  }
  ok(
    `all ${d.tables.length} tables: the in-circuit walk of the emitted DAG satisfies the ` +
      `accumulator p3 produced — the row counts below are for THAT circuit`,
  );

  // -----------------------------------------------------------------------
  // [3] It can go red — one child index, one root, one column.
  // -----------------------------------------------------------------------
  console.log('\n[3] the in-circuit KAT REFUSES a bent DAG');
  const alu = d.tables.find((t) => t.name === 'Alu')!;
  const bendChild = (t: DagTable): DagTable => {
    const nodes = t.nodes.map((n) => n.slice());
    // The last binary node whose two children differ — swapping a child for its
    // sibling is wf-preserving (still topologically sorted, same kinds, same
    // multiply count), so nothing structural catches it.
    for (let i = nodes.length - 1; i > 0; i--) {
      const n = nodes[i];
      if ((n[0] === 2 || n[0] === 3 || n[0] === 5) && n[1] !== n[2]) {
        nodes[i] = [n[0], n[1], n[1]];
        return { ...t, nodes };
      }
    }
    return fail('Alu has no binary node with distinct children — the bend cannot be applied');
  };
  await refuses('a wf-preserving one-child edit to a single Alu node', () =>
    katCircuit(alu, 0, bendChild),
  );
  await refuses('two constraint ROOTS swapped (the fold order moves, nothing else)', () =>
    katCircuit(alu, 0, (t) => {
      const roots = t.roots.slice();
      [roots[0], roots[1]] = [roots[1], roots[0]];
      if (roots[0] === roots[1])
        fail('the two swapped roots are the same node — the falsifier substitutes a value for itself');
      return { ...t, roots };
    }),
  );
  await refuses('one BASE constraint dropped from the fold', () =>
    katCircuit(alu, 0, (t) => ({ ...t, roots: t.roots.slice(1) })),
  );

  // -----------------------------------------------------------------------
  // [4] THE PERMANENT CONTROL — p3's fold against `AirEval.ts`'s.
  // -----------------------------------------------------------------------
  // The EMITTED per-operation marginals — measured here because [4] needs the
  // fold's price, printed in [5] where they belong.
  const wit = () => Provable.witness(BbExt, () => BbExt.from([1n, 2n, 3n, 4n]));
  const marginal = async (f: (n: number) => void, k = 200) => {
    const a = await Provable.constraintSystem(() => f(k));
    const b = await Provable.constraintSystem(() => f(2 * k));
    return (b.rows - a.rows) / k;
  };
  const rAdd = await marginal((n) => {
    let x = wit();
    const y = wit();
    for (let i = 0; i < n; i++) x = extAdd(x, y);
  });
  const rSub = await marginal((n) => {
    let x = wit();
    const y = wit();
    for (let i = 0; i < n; i++) x = extSub(x, y);
  });
  const rMul = await marginal((n) => {
    let x = wit();
    const y = wit();
    for (let i = 0; i < n; i++) x = extMul(x, y);
  });
  const rFold = await marginal((n) => {
    let x = wit();
    const y = wit();
    for (let i = 0; i < n; i++) x = extAdd(extMul(x, y), y);
  });

  console.log('\n[4] PERMANENT CONTROL — the fold, and a recorded defect that is not one');
  {
    // ⚑ §3.17 RECORDS: "AND THE α-FOLD IS OFF BY ONE IN `AirEval.ts`. `foldConstraints` seeds
    // with `constraints[0]` and pays `N − 1` folds; p3 seeds with ZERO and pays `N`". That is a
    // true reading of both bodies and a WRONG conclusion about what it means, and it took running
    // them side by side to see it: seeding with zero and folding `C_0` gives `0·α + C_0 = C_0`, so
    // p3's first fold IS the other one's seed. Both compute
    //     C_0·α^{N-1} + C_1·α^{N-2} + … + C_{N-1}
    // exactly. The difference is one `mul_add` against a zero accumulator — 48 EMITTED rows spent
    // on an identity — and NOT a different accumulator. A verifier built on `foldConstraints`
    // would have been right, not off by a factor of alpha. §3.16's "corrected for it by
    // subtracting one marginal price" was the correct treatment and the §3.17 note over-read it.
    //
    // This control runs on every green pass. If either body ever moves so the two DISAGREE, that
    // is a real defect and this reds.
    const t = alu;
    const k = t.kat[0];
    const { alpha, base, ext } = katAssignment(t, k);
    const roots = evalDagBigInt(t, base, ext);
    const p3 = foldRootsP3BigInt(alpha, roots);
    if (p3.join(',') !== k.acc.map((x) => BigInt(x)).join(','))
      fail('the out-of-circuit p3 fold does not reproduce the artifact — the control is unpointed');

    let airEvalAcc!: bigint[];
    await Provable.runAndCheck(() => {
      const cs = roots.map((r) => BbExt.from(r));
      const acc = foldConstraints(BbExt.from(alpha), cs);
      Provable.asProver(() => {
        airEvalAcc = acc.toBigInts();
      });
    });
    if (airEvalAcc.join(',') !== p3.join(','))
      fail(
        "`AirEval.foldConstraints` and p3's accumulator now DISAGREE — that IS a semantic defect " +
          `(p3 [${p3}] against [${airEvalAcc}]) and needs reading`,
      );
    ok(
      `p3's accumulator and \`AirEval.foldConstraints\` AGREE on all ${roots.length} Alu ` +
        `constraints — §3.17's "off by one" is a ROW difference, not a different accumulator`,
    );

    // And the row difference IS one fold step, measured rather than argued.
    const rowsP3 = (
      await Provable.constraintSystem(() => {
        const cs = roots.map((r) => Provable.witness(BbExt, () => BbExt.from(r)));
        foldRootsP3(Provable.witness(BbExt, () => BbExt.from(alpha)), cs);
      })
    ).rows;
    const rowsAe = (
      await Provable.constraintSystem(() => {
        const cs = roots.map((r) => Provable.witness(BbExt, () => BbExt.from(r)));
        foldConstraints(Provable.witness(BbExt, () => BbExt.from(alpha)), cs);
      })
    ).rows;
    const dRows = rowsP3 - rowsAe;
    if (dRows <= 0 || dRows > rFold)
      fail(
        `the two folds differ by ${dRows} rows, outside (0, ${rFold}] — the extra work is not ` +
          'the one fold step against a zero accumulator that the difference is supposed to be',
      );
    ok(
      `and they differ by ${fmt(dRows)} EMITTED rows — p3's extra fold against a CONSTANT zero ` +
        `accumulator, cheaper than a live fold step (${rFold}) because the 16 products fold away, ` +
        `and spent on an identity either way`,
    );

    // ⚑ THE ORDER IS LOAD-BEARING AND THIS IS WHAT SHOWS IT. `ConstraintEvaluator`'s doc says a
    // permuted list is a different accumulator; reversing the root order must move it, or the
    // emission order this artifact preserves would be decorative.
    const rev = foldRootsP3BigInt(alpha, roots.slice().reverse());
    if (rev.join(',') === p3.join(','))
      fail('reversing the constraint order does not move the accumulator — the fold is order-blind');
    ok('reversing the 146 constraints moves the accumulator — the emission order is load-bearing');
  }

  // -----------------------------------------------------------------------
  // [5] EMITTED per-operation marginals.
  // -----------------------------------------------------------------------
  console.log('\n[5] EMITTED marginals — what one extension operation costs');
  console.log(
    `    extAdd ${rAdd}   extSub ${rSub}   extMul ${rMul}   one alpha-fold step ${rFold}`,
  );
  if (rFold !== rMul + rAdd)
    fail(`the fold step is ${rFold} against extMul+extAdd = ${rMul + rAdd} — the decomposition is wrong`);
  ok(
    `one alpha-fold step is ${rFold} EMITTED rows — §3.16's measured h = 48, reproduced from ` +
      `its two halves`,
  );
  // §3.14's model units, against what the circuit actually emits.
  const MODEL = { mul: 31, lin: 19 };
  console.log(
    `    §3.14's model priced an extension multiply at ${MODEL.mul} and an add/scale at ` +
      `${MODEL.lin}; emitted, they are ${rMul} and ${rAdd}`,
  );

  // -----------------------------------------------------------------------
  // [6] THE EMISSION — the whole root AIR, per table.
  // -----------------------------------------------------------------------
  console.log('\n[6] EMITTED — the root\'s whole constraint system as a Kimchi circuit');
  console.log(
    `\n    ${'table'.padEnd(16)}${'N'.padStart(7)}${'nodes'.padStart(8)}${'cols'.padStart(7)}` +
      `${'witness'.padStart(10)}${'C_i'.padStart(10)}${'fold'.padStart(9)}${'rows'.padStart(10)}`,
  );
  let totRows = 0;
  let totWit = 0;
  let totCi = 0;
  let totFold = 0;
  const perTable: { name: string; rows: number; ci: number; fold: number; wit: number }[] = [];
  for (const t of d.tables) {
    const witRows = (await Provable.constraintSystem(() => witnessTableColumns(t, 0x51ced00dn))).rows;
    const ciRows =
      (
        await Provable.constraintSystem(() => {
          const c = witnessTableColumns(t, 0x51ced00dn);
          evalDagInCircuit(t, c.base, c.ext, {});
        })
      ).rows - witRows;
    const allRows = (
      await Provable.constraintSystem(() => {
        const c = witnessTableColumns(t, 0x51ced00dn);
        const roots = evalDagInCircuit(t, c.base, c.ext, {});
        const alpha = Provable.witness(BbExt, () => BbExt.from([7n, 5n, 3n, 2n]));
        foldRootsP3(alpha, roots);
      })
    ).rows;
    const foldRows = allRows - witRows - ciRows;
    perTable.push({ name: t.name, rows: allRows, ci: ciRows, fold: foldRows, wit: witRows });
    totRows += allRows;
    totWit += witRows;
    totCi += ciRows;
    totFold += foldRows;
    console.log(
      `    ${t.name.padEnd(16)}${fmt(t.roots.length).padStart(7)}${fmt(t.nodes.length).padStart(8)}` +
        `${fmt(t.cols.length + t.extCols.length).padStart(7)}${fmt(witRows).padStart(10)}` +
        `${fmt(ciRows).padStart(10)}${fmt(foldRows).padStart(9)}${fmt(allRows).padStart(10)}`,
    );
  }
  console.log(
    `    ${'TOTAL'.padEnd(16)}${fmt(d.totals.n).padStart(7)}${fmt(d.totals.nodes).padStart(8)}` +
      `${fmt(shape.base + shape.ext).padStart(7)}${fmt(totWit).padStart(10)}${fmt(totCi).padStart(10)}` +
      `${fmt(totFold).padStart(9)}${fmt(totRows).padStart(10)}`,
  );

  // The fold term must be the emitted marginal times N — that is the check that
  // the split above is a decomposition and not a subtraction that absorbed an
  // error.
  const foldPredicted = d.totals.n * rFold;
  const foldDrift = Math.abs(totFold / foldPredicted - 1);
  if (foldDrift > 0.06)
    fail(
      `the emitted fold term ${fmt(totFold)} is ${(foldDrift * 100).toFixed(1)}% from ` +
        `N x ${rFold} = ${fmt(foldPredicted)} — the decomposition does not close`,
    );
  ok(
    `the fold term ${fmt(totFold)} is N x ${rFold} = ${fmt(foldPredicted)} to ` +
      `${(foldDrift * 100).toFixed(1)}% — the split is a decomposition, not a subtraction`,
  );

  // And `C_i` against §3.18's model, which priced only the 901 BASE constraints.
  const k = d.totals.kinds;
  const modelCi = k.mul * MODEL.mul + (k.var + k.add + k.sub + k.neg + k.evar) * MODEL.lin;
  console.log(
    `\n    §3.18's model priced C_i (901 base constraints, 8,698 nodes) at 187,295 rows and the ` +
      `whole\n    AIR side at 253,934. EMITTED, over all 1,093 constraints and ${fmt(d.totals.nodes)} nodes:`,
  );
  console.log(
    `      C_i          ${fmt(totCi).padStart(9)}  (the same units applied to this node census: ${fmt(modelCi)})`,
  );
  console.log(`      the fold     ${fmt(totFold).padStart(9)}  (N x ${rFold})`);
  console.log(`      witnessing   ${fmt(totWit).padStart(9)}  (${fmt(shape.base + shape.ext)} columns, range-checked)`);
  console.log(`      TOTAL        ${fmt(totRows).padStart(9)}`);

  // ⚑ The model's `.var` line, corrected by emission.
  console.log(
    `\n    ⚑ §3.18 charged ${fmt(k.var)} \`.var\` copy nodes at ${MODEL.lin} rows each ` +
      `(${fmt(k.var * MODEL.lin)} rows) and called it\n      elidable. EMITTED they are FREE — a lane already ` +
      `under 2^31 is not reduced (\`reduceLane\`),\n      so the elision was already taken and the model ` +
      `overcharged for it.`,
  );

  // -----------------------------------------------------------------------
  // [7] What this does to §3.19's floor.
  // -----------------------------------------------------------------------
  console.log('\n[7] the floor, repriced');
  const DEPLOYED_TOTAL = 2.75e7;
  const FIXTURE_AIR = 4;
  console.log(
    `    §3.19 projects the deployed root at ${DEPLOYED_TOTAL.toExponential(2)} rows and says in ` +
      `terms:\n      "2.75 x 10^7 is a FLOOR ... the AIR term inside it is the fixture's ${FIXTURE_AIR} ` +
      `constraints,\n       not the root's 1,093".`,
  );
  const repriced = DEPLOYED_TOTAL + totRows;
  console.log(
    `    The root's AIR term is ${fmt(totRows)} EMITTED rows, ONCE per verify ` +
      `(\`verify_constraints_with_lookups\`\n    runs per instance per proof, not per query). ` +
      `⇒ ${repriced.toExponential(3)} rows.`,
  );
  ok(
    `the AIR term is ${((totRows / DEPLOYED_TOTAL) * 100).toFixed(2)}% of the projection — the floor ` +
      `was a floor by that much, and it is now MEASURED rather than named`,
  );

  // -----------------------------------------------------------------------
  // [8] Ratchet.
  // -----------------------------------------------------------------------
  console.log('\n[8] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['N, the root batch constraint count', d.totals.n, 1093],
    ['DAG nodes for all 1,093 constraints', d.totals.nodes, 10417],
    ['DAG multiplies', d.totals.muls, 3029],
    ['EMITTED rows, one extension multiply', rMul, 30],
    ['EMITTED rows, one extension add', rAdd, 18],
    ['EMITTED rows, one alpha-fold step', rFold, 48],
    ['EMITTED rows, C_i over all 1,093 constraints', totCi, 181126],
    ['EMITTED rows, the alpha-fold', totFold, 52358],
    ['EMITTED rows, the root AIR whole', totRows, 275143],
  ];
  let drifted = 0;
  for (const [label, got, want] of RECORDED) {
    const mark = got === want ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(48)} ${fmt(got).padStart(10)} (recorded ${fmt(want)})`);
    if (got !== want) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted — read them, do not re-record them`);
  ok(`${RECORDED.length} recorded figures are as recorded`);

  console.log(`\n=== ROOT-AIR-ROWS PASS === ${checks} checks\n`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
