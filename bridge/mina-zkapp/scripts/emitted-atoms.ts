import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { randomBytes } from 'node:crypto';
import {
  DreggProofShape,
  makeDreggProofVerifyProgram,
  shapeOf,
} from '../src/DreggProofVerify.js';
import { rootAirDag } from '../src/RootAirDag.js';

// ---------------------------------------------------------------------------
// LEG 14a — THE ATOM ROW LIST, EMITTED.
//
// ⚑ WHAT THIS EXISTS TO KILL, in §3.21's own words:
//
//   "The atom model's row figures are §3.19's measured marginals and its
//    aggregate matches §3.19's projection to 0.01%, but a 2.75 x 10^7-row
//    circuit has never been emitted. 591 is a schedule over a measured MODEL,
//    not over an emitted row list."
//
// The model takes FIVE aggregate readings and DIVIDES them across 27,590 atoms:
// `perArith = (deployedQueryWalk - pathLevels * PERM_ROWS) / (layers + 1)` and
// `tailRows / nTail`. Those two divisions are the modelling. Everything else in
// the model is a measured marginal.
//
// This leg replaces the divisions with IN-CONTEXT MARGINALS on the deployed
// program itself: a fold LAYER's price is `rows(layers = L) - rows(layers =
// L-1)` on the real deployed-geometry verifier, an input-path LEVEL's is
// `rows(pathDepth = d) - rows(pathDepth = d-1)`, and the transcript tail is what
// is left after every atom with its own marginal is subtracted.
//
// ⚑ A MARGINAL IS NOT A STANDALONE PROBE, AND THE DIFFERENCE IS LARGE. A
// Poseidon2 compression measured on its own is 2,632.5 rows; the same
// compression as one more Merkle level inside the deployed walk carries a
// `condSwap` and the surrounding bound bookkeeping. Measured standalone, the
// per-column DEEP term is 66 rows; §3.19's in-context marginal for the same
// column is 481, because the column also widens the MMCS leaf row. Only the
// in-context number prices an atom inside a step, so only in-context numbers are
// written here.
//
// ⚑ AND THE WALL IS REAL: `analyzeMethods` on a ~1.7 M-row circuit aborts inside
// kimchi's 32-bit wasm allocator (§3.19), so every measurement below is at ONE
// query. The per-query structure is then a MULTIPLICITY, not another division.
// ---------------------------------------------------------------------------

const WORKDIR = process.env.ATOM_WORKDIR ?? resolve(process.cwd(), '.atoms');
const OUT = resolve(WORKDIR, 'emitted-atoms.json');

const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const fmt = (n: number) => n.toLocaleString('en-US');
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit/src/bin/mina_stark_fixture.rs')))
    fail(`the dregg-side proof emitter is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}
const ROOT = repoRoot();

let built = false;
function mint(db: number, lb: number, nq: number, qpow: number, seed: number): any {
  if (!built) {
    const t = Date.now();
    execFileSync(
      'cargo',
      ['build', '-p', 'dregg-circuit', '--release', '--bin', 'mina_stark_fixture'],
      { cwd: ROOT, stdio: ['ignore', 'ignore', 'inherit'] },
    );
    console.log(`    emitter built in ${secs(t)}`);
    built = true;
  }
  const out = execFileSync(
    resolve(ROOT, 'target/release/mina_stark_fixture'),
    [db, lb, nq, qpow, seed].map(String).concat(['none']),
    { encoding: 'utf8', maxBuffer: 1 << 26 },
  );
  return JSON.parse(out);
}

async function rowsOf(sh: DreggProofShape): Promise<number> {
  const { prog } = makeDreggProofVerifyProgram(sh);
  const a = await prog.analyzeMethods();
  return (a as any).verifyDreggProof.rows;
}

/** The deployed FRI geometry, with `layers`, the input path depth and the
 *  opened-column count as knobs — the three things this leg differentiates. */
function deployed(
  base: DreggProofShape,
  o: { layers: number; inputDepth: number; cols: number; queries: number },
): DreggProofShape {
  return {
    ...base,
    constraints: undefined,
    deriveChallenges: false,
    knobs: {
      ...base.knobs,
      layers: o.layers,
      logGlobalMaxHeight: 22,
      indexBits: 22,
      logBlowup: 6,
      numQueries: o.queries,
    },
    logGlobalMaxHeight: 22,
    // The deployed schedule is `21 - r` for round `r`; a shorter run keeps the
    // same head so the marginal is the LAST layer, whose path is the shortest.
    commitPathDepths: Array.from({ length: o.layers }, (_, i) => 21 - i),
    batches: base.batches.map((b, i) => ({
      matrices: b.matrices.map((m) => ({
        ...m,
        logHeight: 22,
        numCols: i === 0 ? o.cols : m.numCols,
      })),
      pathDepth: o.inputDepth,
    })),
    air: { ...base.air, width: o.cols },
  };
}

async function main() {
  console.log('\n=== EMITTED-ATOMS — the atom row list, measured not divided (leg 14a) ===\n');
  mkdirSync(WORKDIR, { recursive: true });

  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  const fx = mint(1, 1, 1, 16, seed);
  if (fx.kind !== 'dregg-uni-stark-fixture') fail(`the emitter returned ${fx.kind}`);
  const SHAPE = shapeOf(fx, {});
  const COLS0 = 3;
  console.log(`    fixture minted (seed ${seed}); the base shape carries ${COLS0} trace columns`);

  const nBatches = SHAPE.batches.length;
  const at = async (
    label: string,
    o: { layers: number; inputDepth: number; cols: number; queries: number },
  ) => {
    const t = Date.now();
    const r = await rowsOf(deployed(SHAPE, o));
    console.log(
      `    ${label.padEnd(46)} ${fmt(r).padStart(10)} rows   (${secs(t)}, layers ${o.layers}, ` +
        `depth ${o.inputDepth}, cols ${o.cols})`,
    );
    return r;
  };

  // ── the reference point: ONE query, deployed, no AIR, challenges witnessed ──
  const base = await at('the deployed query WALK, 1 query', {
    layers: 16,
    inputDepth: 22,
    cols: COLS0,
    queries: 1,
  });

  // ── one fold LAYER, as an in-context marginal ────────────────────────────
  // Layer 15's path is 21-15 = 6 levels; layer 14's is 7. Two deltas at two
  // different depths separate the ROUND's arithmetic from the PATH's levels,
  // which is exactly what the model divided instead of measuring.
  const l15 = await at('the same at 15 fold layers', {
    layers: 15,
    inputDepth: 22,
    cols: COLS0,
    queries: 1,
  });
  const l14 = await at('the same at 14 fold layers', {
    layers: 14,
    inputDepth: 22,
    cols: COLS0,
    queries: 1,
  });
  // dropping layer 15 removes 1 round + 6 path levels; dropping layer 14 too
  // removes 1 round + 7 path levels.
  const d15 = base - l15;
  const d14 = l15 - l14;
  const foldPathRows = d14 - d15; //           one more path level
  const foldArithRows = d15 - 6 * foldPathRows; // the round itself
  if (foldPathRows <= 0 || foldArithRows <= 0)
    fail(
      `the fold decomposition is not positive: path ${foldPathRows}, arith ${foldArithRows} ` +
        `(deltas ${d15} / ${d14}) — the two layers are not differing by what the schedule says`,
    );

  // ── one input-path LEVEL ─────────────────────────────────────────────────
  const p21 = await at('the same at input path depth 21', {
    layers: 16,
    inputDepth: 21,
    cols: COLS0,
    queries: 1,
  });
  const inputPathRows = (base - p21) / nBatches;
  if (inputPathRows <= 0)
    fail(`the input-path marginal is ${inputPathRows} over ${nBatches} batches — not positive`);

  // ── the per-column marginals, in context ─────────────────────────────────
  const WIDE = COLS0 + 32;
  const w1 = await at(`the same at ${WIDE} trace columns, 1 query`, {
    layers: 16,
    inputDepth: 22,
    cols: WIDE,
    queries: 1,
  });
  const perColOneQuery = (w1 - base) / 32;

  // ── what is LEFT is the transcript tail and the closing evaluation ───────
  const accountedPerQuery =
    16 * foldArithRows +
    Array.from({ length: 16 }, (_, r) => 21 - r).reduce((a, b) => a + b, 0) * foldPathRows +
    nBatches * 22 * inputPathRows;
  const residual = base - accountedPerQuery;
  console.log(
    `\n    of the ${fmt(base)}-row deployed walk, ${fmt(accountedPerQuery)} is accounted for by ` +
      `atoms with\n    their own in-context marginal; the residual is ${fmt(residual)} ` +
      `(${((residual / base) * 100).toFixed(1)}%)`,
  );
  if (residual <= 0)
    fail(
      `the atoms with marginals already exceed the walk by ${fmt(-residual)} rows — the ` +
        'decomposition double-counts and the schedule built on it would be wrong',
    );

  // ── the AIR atoms, from leg 13's emission ────────────────────────────────
  const d = rootAirDag();
  const air = {
    nodes: d.totals.nodes,
    kinds: d.totals.kinds,
    n: d.totals.n,
    // EMITTED in leg 13; re-stated here so the schedule reads ONE table.
    rowsMul: 30,
    rowsLin: 18,
    rowsCopy: 0,
    rowsFold: 48,
    rowsWitnessPerCol: 26, // 41,659 / 1,602, EMITTED
    totalRows: 275143,
  };

  const out = {
    kind: 'dregg-emitted-atoms',
    generator: 'bridge/mina-zkapp/scripts/emitted-atoms.ts',
    geometry: { logD0: 22, layers: 16, logBlowup: 6, inputDepth: 22, nBatches, queries: 19 },
    measured: {
      deployedWalkOneQuery: base,
      walk15Layers: l15,
      walk14Layers: l14,
      walkInputDepth21: p21,
      wideOneQuery: w1,
      wideCols: WIDE,
      baseCols: COLS0,
    },
    atoms: {
      foldPath: foldPathRows,
      foldArith: foldArithRows,
      inputPath: inputPathRows,
      perColumnOneQuery: perColOneQuery,
      residualPerQuery: residual,
    },
    air,
  };
  writeFileSync(OUT, JSON.stringify(out, null, 1));

  console.log('\n    EMITTED per-atom rows, in context:');
  console.log(`      one commit-phase path LEVEL          ${fmt(foldPathRows)}`);
  console.log(`      one fold ROUND's arithmetic          ${fmt(foldArithRows)}`);
  console.log(`      one input-phase path LEVEL           ${fmt(inputPathRows)}`);
  console.log(`      one opened column, at one query      ${fmt(perColOneQuery)}`);
  console.log(`      the residual per query               ${fmt(residual)}`);
  console.log(`      one AIR DAG multiply / add / fold    30 / 18 / 48`);
  console.log(`\n    wrote ${OUT}`);
  console.log('\n=== EMITTED-ATOMS PASS ===\n');
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
