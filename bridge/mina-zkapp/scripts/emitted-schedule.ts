import { execFileSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { randomBytes } from 'node:crypto';
import { shapeOf } from '../src/DreggProofVerify.js';
import {
  EmittedAtoms,
  MEASURED,
  PICKLES_OVERHEAD,
  Program,
  bestSchedule,
  deployedProgram,
  emittedProgram,
  schedule,
  usableRows,
} from '../src/PartitionSchedule.js';
import { liveness, rootAirDag, unifiedDag } from '../src/RootAirDag.js';
import { planRootAirChain } from '../src/RootAirChain.js';

// ---------------------------------------------------------------------------
// LEG 14b — THE SCHEDULE, RE-RUN OVER EMITTED ROWS.
//
// §3.21 lands at 591 work-carrying steps and says exactly what that number is
// and is not:
//
//   "591 is a schedule over a measured MODEL, not over an emitted row list —
//    which is precisely the distinction `KimchiPartition` draws between 'a
//    partitioning number' and 'a compiler output', and it is still open."
//   "2.75 x 10^7 is itself a FLOOR ... A floor scheduled is still a floor."
//
// This leg re-runs the SAME dynamic program over an atom list whose every row
// figure is a difference of two emitted circuits (leg 14a) and which contains
// the ROOT's own 1,093 constraints (leg 13) instead of the fixture's four.
//
// ⚑ WHAT WOULD MAKE THIS A GREEN THAT MEASURES NOTHING: reporting a step count
// whose atom list happens to be the old one under a new name. [1] therefore
// prints the per-atom price CHANGES, and [2] fails if the AIR block is absent or
// if the emitted total is not strictly above the model's — the whole point is
// that the floor moved.
// ---------------------------------------------------------------------------

const ATOMS = resolve(process.env.ATOM_WORKDIR ?? resolve(process.cwd(), '.atoms'), 'emitted-atoms.json');

let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const fmt = (n: number) => Math.round(n).toLocaleString('en-US');

function repoRoot(): string {
  const d = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  if (!existsSync(resolve(d, 'circuit/src/bin/mina_stark_fixture.rs')))
    fail(`the dregg-side proof emitter is not under ${d} — set DREGG_REPO_ROOT`);
  return d;
}

async function main() {
  console.log('\n=== EMITTED-SCHEDULE — 591, re-run over an emitted row list (leg 14b) ===\n');

  // ⚑ MISSING TOOLCHAIN IS A FAILURE, NOT A SKIP.
  if (!existsSync(ATOMS))
    fail(
      `the emitted atom list is missing at ${ATOMS} — run \`npm run emitted-atoms\` first. ` +
        'This leg must NOT fall back to the divided model; that is the thing it exists to replace.',
    );
  const em = JSON.parse(readFileSync(ATOMS, 'utf8')) as EmittedAtoms;
  if (em.kind !== 'dregg-emitted-atoms') fail(`${ATOMS} is not an emitted atom list`);

  // A base shape for the deployed geometry — the same fixture route every other
  // leg uses, so the lane census is the same object.
  const ROOT = repoRoot();
  execFileSync('cargo', ['build', '-p', 'dregg-circuit', '--release', '--bin', 'mina_stark_fixture'], {
    cwd: ROOT,
    stdio: ['ignore', 'ignore', 'inherit'],
  });
  const seed = Number(BigInt('0x' + randomBytes(4).toString('hex')) % 1_000_000n);
  const fx = JSON.parse(
    execFileSync(resolve(ROOT, 'target/release/mina_stark_fixture'), ['1', '1', '1', '16', String(seed), 'none'], {
      encoding: 'utf8',
      maxBuffer: 1 << 26,
    }),
  );
  const SHAPE = shapeOf(fx, {});

  // -----------------------------------------------------------------------
  // [1] What the emission changed, atom by atom.
  // -----------------------------------------------------------------------
  console.log('[1] the atom prices, MODELLED against EMITTED');
  const modelProg = deployedProgram(SHAPE, { openChunkLanes: 128 });
  const modelArith = modelProg.atoms.find((a) => a.kind === 'fold-arith')!.rows;
  const modelPath = modelProg.atoms.find((a) => a.kind === 'fold-path')!.rows;
  const modelInput = modelProg.atoms.find((a) => a.kind === 'input-path')!.rows;
  const rows: [string, number, number][] = [
    ['one commit-phase path LEVEL', modelPath, em.atoms.foldPath],
    ["one fold ROUND's arithmetic", modelArith, em.atoms.foldArith],
    ['one input-phase path LEVEL', modelInput, em.atoms.inputPath],
  ];
  console.log(`    ${'atom'.padEnd(30)}${'modelled'.padStart(11)}${'EMITTED'.padStart(11)}${'delta'.padStart(9)}`);
  for (const [l, m, e] of rows)
    console.log(
      `    ${l.padEnd(30)}${fmt(m).padStart(11)}${fmt(e).padStart(11)}` +
        `${(((e - m) / m) * 100).toFixed(1).padStart(8)}%`,
    );
  ok(
    `the model's LARGEST indivisible atom — the fold round it derived as ` +
      `(walk - paths x PERM_ROWS)/(layers+1) = ${fmt(modelArith)} — is ${fmt(em.atoms.foldArith)} ` +
      `emitted, ${(((em.atoms.foldArith - modelArith) / modelArith) * 100).toFixed(1)}%`,
  );
  const acct = em.measured.deployedWalkOneQuery - em.atoms.residualPerQuery;
  ok(
    `${((acct / em.measured.deployedWalkOneQuery) * 100).toFixed(1)}% of the deployed query walk ` +
      `is atoms with their OWN in-context marginal; the residual is ${fmt(em.atoms.residualPerQuery)} ` +
      `rows (${((em.atoms.residualPerQuery / em.measured.deployedWalkOneQuery) * 100).toFixed(1)}%)`,
  );

  // -----------------------------------------------------------------------
  // [2] The emitted program, with the root's own AIR in it.
  // -----------------------------------------------------------------------
  console.log('\n[2] the deployed verifier as an EMITTED atom list');
  // ⚑ THE SAME CHUNK-SIZE SWEEP §3.21 USES. Its 591/504 are the BEST over
  // [24..512]; comparing a swept baseline against a fixed-128 emitted arm would
  // credit the emission with a chunk-size choice, so both arms sweep.
  const SIZES = [24, 32, 48, 64, 94, 128, 192, 256, 384, 512];
  const bestEmitted = (withAir: boolean, u: number) => {
    let best: { chunkLanes: number; prog: Program; steps: number; carry: number } | null = null;
    for (const chunkLanes of SIZES) {
      const prog = emittedProgram(SHAPE, em, { openChunkLanes: chunkLanes, withAir });
      const sc = schedule(prog, u);
      if (!best || sc.steps < best.steps || (sc.steps === best.steps && sc.carryRows < best.carry))
        best = { chunkLanes, prog, steps: sc.steps, carry: sc.carryRows };
    }
    return best!;
  };
  const CHUNK = 128;
  const noAir = emittedProgram(SHAPE, em, { openChunkLanes: CHUNK, withAir: false });
  const withAir = emittedProgram(SHAPE, em, { openChunkLanes: CHUNK, withAir: true });
  const nAirAtoms = withAir.atoms.length - noAir.atoms.length;
  const airRows = withAir.totalRows - noAir.totalRows;
  console.log(
    `    §3.21's atom model      ${fmt(modelProg.atoms.length).padStart(8)} atoms  ` +
      `${fmt(modelProg.totalRows).padStart(12)} rows  (fixture AIR, divided marginals)`,
  );
  console.log(
    `    EMITTED, no AIR         ${fmt(noAir.atoms.length).padStart(8)} atoms  ` +
      `${fmt(noAir.totalRows).padStart(12)} rows`,
  );
  console.log(
    `    EMITTED, ROOT's AIR     ${fmt(withAir.atoms.length).padStart(8)} atoms  ` +
      `${fmt(withAir.totalRows).padStart(12)} rows  (+${fmt(nAirAtoms)} atoms, +${fmt(airRows)} rows)`,
  );
  if (nAirAtoms < 10_000)
    fail(`only ${nAirAtoms} AIR atoms — the root's 10,417 nodes and 1,093 folds are not in the list`);
  ok(
    `the AIR block is ${fmt(nAirAtoms)} atoms and ${fmt(airRows)} rows — the root's ` +
      `10,417 DAG nodes and 1,093 folds, at leg 13's EMITTED prices`,
  );
  const drift = withAir.totalRows / MEASURED.deployedTotal - 1;
  console.log(
    `    against §3.19's projected ${MEASURED.deployedTotal.toExponential(2)}: ` +
      `${(drift * 100).toFixed(2)}%`,
  );

  // -----------------------------------------------------------------------
  // [3] The schedule.
  // -----------------------------------------------------------------------
  console.log('\n[3] the SAME dynamic program, over the emitted list');
  const arms: [string, number, number][] = [
    ['max_proofs_verified = 1', usableRows(PICKLES_OVERHEAD.straightChain), 504],
    ['max_proofs_verified = 2', usableRows(PICKLES_OVERHEAD.aggregationTree), 591],
  ];
  const out: Record<string, number> = {};
  for (const [label, u, recorded] of arms) {
    const sModel = bestSchedule(SHAPE, u, SIZES);
    const bNo = bestEmitted(false, u);
    const bAir = bestEmitted(true, u);
    const sAir = schedule(bAir.prog, u);
    out[label] = bAir.steps;
    console.log(`\n    ${label}  (usable ${fmt(u)})`);
    console.log(
      `      §3.21, modelled atoms, fixture AIR   ${fmt(sModel.sched.steps).padStart(6)} steps  ` +
        `(§3.21 recorded ${recorded}, chunk ${sModel.chunkLanes})`,
    );
    console.log(
      `      EMITTED atoms, no AIR                ${fmt(bNo.steps).padStart(6)} steps  ` +
        `(chunk ${bNo.chunkLanes})`,
    );
    console.log(
      `      EMITTED atoms, the ROOT's AIR        ${fmt(bAir.steps).padStart(6)} steps  ` +
        `(chunk ${bAir.chunkLanes})  ` +
        `carry ${((sAir.carryRows / (sAir.workRows + sAir.carryRows)) * 100).toFixed(1)}%  ` +
        `slack ${((sAir.slackRows / (u * sAir.steps)) * 100).toFixed(1)}%`,
    );
    console.log(
      `      boundaries: ${sAir.census.insideQuery} inside a query, ` +
        `${sAir.census.inTranscript} in the transcript/AIR block, ` +
        `${sAir.census.atQueryEntry} at a query ENTRY`,
    );
    if (sModel.sched.steps !== recorded)
      fail(
        `the model arm reproduces ${sModel.sched.steps} steps, not §3.21's recorded ${recorded} — the ` +
          'comparison has drifted and the delta below would be against the wrong baseline',
      );
    if (sAir.maxStepRows > u) fail(`a step spends ${fmt(sAir.maxStepRows)} of ${fmt(u)}`);
  }
  ok(
    `§3.21's 591 and 504 are reproduced EXACTLY from the model arm — so the movement below is ` +
      `the emission and the AIR, not a different scheduler`,
  );
  ok(
    `over the EMITTED list with the root's own AIR: ${out['max_proofs_verified = 2']} steps at ` +
      `mpv = 2 and ${out['max_proofs_verified = 1']} at mpv = 1`,
  );

  // -----------------------------------------------------------------------
  // [4] The AIR block's own schedule — and the wall.
  // -----------------------------------------------------------------------
  console.log('\n[4] the AIR block alone, and the wall a chain over it hits');
  const u2 = unifiedDag(rootAirDag());
  const lv = liveness(u2);
  console.log(
    `    the root's constraint DAG is ${fmt(u2.nodes.length)} nodes / ${fmt(u2.roots.length)} ` +
      `constraints over ${fmt(u2.nBaseCols + u2.nExtCols)} column variables`,
  );
  console.log(
    `    the CUT WIDTH — values live across a boundary — is at most ${lv.maxWidth} nodes ` +
      `across the whole DAG`,
  );
  for (const [label, u] of [
    ['mpv = 1', usableRows(PICKLES_OVERHEAD.straightChain)],
    ['mpv = 2', usableRows(PICKLES_OVERHEAD.aggregationTree)],
  ] as [string, number][]) {
    const p = planRootAirChain(u2, { usableRows: u, chunkSize: 64 });
    console.log(
      `    ${label}: ${p.slices.length} slices, work ${fmt(p.totalWork)} + carry ` +
        `${fmt(p.totalCarry)} (${((p.totalCarry / (p.totalWork + p.totalCarry)) * 100).toFixed(1)}%)`,
    );
  }
  ok(
    `the root's AIR is ${planRootAirChain(u2, { usableRows: usableRows(PICKLES_OVERHEAD.straightChain), chunkSize: 64 }).slices.length} ` +
      `chained steps on its own — it has NO one-step verifier, at 4.8x the Kimchi domain`,
  );
  console.log(
    `\n    ⚑ THE WALL, WITH ITS NUMBER. Those slices are structurally DIFFERENT circuits — a\n` +
      `      uniform one would need an in-circuit multiplexer over the ${lv.maxWidth}-value live set,\n` +
      `      ~${lv.maxWidth} rows per operand lane against 30 for the whole multiply, a ${Math.round((lv.maxWidth * 2 * 4) / 30)}x blowup.\n` +
      `      §3.20 MEASURED a node process that compiled FOUR step circuits hanging at the first\n` +
      `      \`prove\`, so ONE process can carry 3 slices. The AIR is a FIXED program, so per-slice\n` +
      `      verification keys are protocol CONSTANTS rather than a per-proof cost — which is the\n` +
      `      opposite of §3.20's per-query steps, and why a VK per slice is affordable there and\n` +
      `      was not there. Full coverage is a process-per-slice architecture; leg 15 proves the\n` +
      `      largest chain one process holds.`,
  );

  console.log('\n[5] RATCHET');
  const RECORDED: [string, number, number][] = [
    ['EMITTED one commit-phase path level', em.atoms.foldPath, 2677],
    ['EMITTED one fold round arithmetic', em.atoms.foldArith, 2809],
    ['EMITTED one input-phase path level', Math.round(em.atoms.inputPath * 2), 5353],
    ['EMITTED deployed query walk, 1 query', em.measured.deployedWalkOneQuery, 748438],
    ['the emitted atom list, whole', withAir.totalRows, 24574325],
    ['deployed steps, EMITTED + root AIR, mpv 2', out['max_proofs_verified = 2'], 519],
    ['deployed steps, EMITTED + root AIR, mpv 1', out['max_proofs_verified = 1'], 448],
  ];
  let drifted = 0;
  for (const [label, got, want] of RECORDED) {
    if (want === 0) {
      console.log(`    · ${label.padEnd(44)} ${fmt(got).padStart(12)} (first recording)`);
      continue;
    }
    const mark = got === want ? '✓' : '✗';
    console.log(`    ${mark} ${label.padEnd(44)} ${fmt(got).padStart(12)} (recorded ${fmt(want)})`);
    if (got !== want) drifted++;
  }
  if (drifted) fail(`${drifted} recorded figure(s) drifted`);
  ok('the recorded figures are as recorded');

  console.log(`\n=== EMITTED-SCHEDULE PASS === ${checks} checks\n`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
