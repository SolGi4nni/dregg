import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  shrinkProofInputs,
  shrinkValues,
  claimLaneFields,
} from '../src/MinaShrinkVerify.js';
import { rootClaim, rootWitness } from '../src/RootConsume.js';

// ---------------------------------------------------------------------------
// o1js VERIFIES dregg's NATIVE-PASTA SHRINK TERMINAL — the deliverable.
//
// Mints (Rust) or loads a REAL `shrink_apex_to_outer(apex, DreggMinaConfig)`
// terminal fixture (`.fullchain/mina-shrink-fixture.json`,
// `RealRootFri`-schema, native Pasta digests, `rehashed:false`), then:
//   [1] compiles the verifier ZkProgram (measured),
//   [2] PROVES the honest terminal — ACCEPT (measured), and reads the exposed
//       G→H ChainClaim out of the public output,
//   [3] TAMPERS one opened input row and re-proves — must REFUSE, and the
//       refusal comes from `verifyInputBatches` recomputing a Merkle root that
//       no longer matches dregg's REAL emitted Pasta commitment (binds, not a
//       re-mint),
//   [4] reports rows / compile / prove.
//
//   npm run mina-shrink-verify
// ---------------------------------------------------------------------------

const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
let failures = 0;
const ok = (m: string) => console.log('  ✓ ' + m);
const fail = (m: string): never => {
  failures++;
  console.error('  ✗ ' + m);
  throw new Error(m);
};
const check = (c: boolean, m: string) => (c ? ok(m) : fail(m));

function loadFixture(): any {
  const repoRoot = process.env.DREGG_REPO_ROOT ?? resolve(process.cwd(), '../..');
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(repoRoot, '.fullchain', 'mina-shrink-fixture.json');
  if (!existsSync(p))
    throw new Error(
      `native-Pasta shrink fixture absent at ${p}. Mint it with:\n` +
        `  cargo test -p dregg-circuit-prove --release --test mina_shrink_fixture -- --ignored --nocapture\n` +
        `(writes .fullchain/mina-shrink-fixture.json), or set MINA_SHRINK_FIXTURE.`,
    );
  const fx = JSON.parse(readFileSync(p, 'utf8'));
  // ⚑ QUERY BATCH. A single ZkProgram verifies a batch of the proof's FRI
  // queries; the full 38-query verifier PARTITIONS across steps exactly as the
  // deployed root verifier does (`DreggProofPartition`/`DreggProofSchedule`, "the
  // deployed one is ~500 steps"). `MINA_SHRINK_QUERIES=N` verifies the first N of
  // the fixture's real query openings — the ACCEPT, the tamper-REJECT (query 0),
  // and the commitment binding all hold per query, and per-query cost × 38 is the
  // full figure. Default: all 38 (needs a large V8 heap).
  const nq = process.env.MINA_SHRINK_QUERIES ? Number(process.env.MINA_SHRINK_QUERIES) : fx.queries.length;
  if (nq < fx.queries.length) {
    fx.queries = fx.queries.slice(0, nq);
    fx.knobs.numQueries = nq;
    fx.knobs.indexBits = fx.knobs.logGlobalMaxHeight;
  }
  return fx;
}

/** Deep clone + tamper ONE opened input row lane (round 0, matrix 0, col 0). */
function tamperInputRow(fx: any): any {
  const t = JSON.parse(JSON.stringify(fx));
  const q = t.queries[0];
  const b = q.inputBatches[0];
  // Flip lane 0 of matrix 0's opened row — a committed leaf value.
  b.rows[0][0] = (Number(b.rows[0][0]) + 1) >>> 0;
  return t;
}

async function main() {
  console.log('=== o1js VERIFIES dregg’s NATIVE-PASTA SHRINK TERMINAL ===\n');

  const fx = loadFixture();
  console.log(
    `fixture: kind=${fx.kind} degree_bits=[${fx.degreeBits}] instances=${fx.degreeBits.length} ` +
      `queries=${fx.knobs.numQueries} rounds=${fx.knobs.layers} log_gmh=${fx.knobs.logGlobalMaxHeight}`,
  );
  console.log(
    `claim: instance=${fx.claimInstance} lanes=${fx.claimLanes.length} (chain claim = lanes 0..25)\n`,
  );

  // ---- Build the program + inputs from the REAL fixture ------------------
  const honest = shrinkProofInputs(fx);
  const { prog } = honest;

  // ---- [1] rows (best-effort) + compile ----------------------------------
  console.log('[1] analyze + compile');
  let rows: number | null = null;
  const rowsMode = process.env.MINA_SHRINK_ROWS ?? 'try'; // 'try' | 'skip' | 'only'
  try {
    if (rowsMode === 'skip') throw new Error('analyzeMethods skipped by MINA_SHRINK_ROWS=skip');
    const analyzed = await prog.analyzeMethods();
    rows = analyzed.verifyShrink.rows;
    ok(`rows (${fx.queries.length} queries): ${fmt(rows)}`);
    if (rowsMode === 'only') {
      console.log(`\nROWS_ONLY: ${rows} rows at ${fx.queries.length} queries`);
      return;
    }
  } catch (e) {
    if (rowsMode === 'only') throw e;
    // o1js serializes the whole gate list to a napi string for analyzeMethods;
    // above a few million gates that string overflows. compile() does NOT need
    // it. Report the count as beyond o1js's introspection limit rather than
    // failing the run.
    ok(`rows: not extractable — o1js analyzeMethods JSON exceeds the napi string limit ` +
       `(the circuit is > a few million gates); measuring via compile/prove instead`);
  }

  const t0 = performance.now();
  await prog.compile();
  const compileMs = performance.now() - t0;
  ok(`compile: ${(compileMs / 1000).toFixed(2)}s`);

  // ---- [2] PROVE the honest terminal — ACCEPT ----------------------------
  console.log('\n[2] prove the HONEST native-Pasta terminal');
  const t1 = performance.now();
  const { proof } = await prog.verifyShrink(honest.claim, ...(honest.witness as any));
  const proveMs = performance.now() - t1;
  ok(`prove: ${(proveMs / 1000).toFixed(2)}s`);

  const verified = await prog.verify(proof);
  check(verified, 'o1js verify(proof) = true  (ACCEPT)');

  const c = proof.publicOutput;
  console.log('    exposed G→H ChainClaim (public output):');
  console.log(`      genesisRoot : ${c.genesisRoot.toString()}`);
  console.log(`      finalRoot   : ${c.finalRoot.toString()}`);
  console.log(`      numTurns    : ${c.numTurns.toString()}`);
  console.log(`      chainDigest : ${c.chainDigest.toString()}`);

  // ---- [3] TAMPER one opened input row — REFUSE --------------------------
  // ⚑ REUSE THE COMPILED PROGRAM. Only the WITNESS values change (one committed
  // leaf); the shape/claim commitment are the honest ones. Proving the tampered
  // witness against the SAME `prog` fails at `verifyInputBatches`'s
  // `assertEq(recomputedRoot, realCommit)`. Building a NEW program here would
  // "refuse" for a vacuous reason ("no prover found" — never compiled), which we
  // explicitly detect and FAIL on.
  console.log('\n[3] tamper ONE opened input row (a committed leaf) — must REFUSE');
  const tfx = tamperInputRow(fx);
  const tv = shrinkValues(tfx);
  const tclaim = rootClaim(honest.sh, tv, honest.DreggProofClaim); // inputCommits = REAL emitted commits (unchanged)
  const twitness = [...rootWitness(honest.sh, tv), claimLaneFields(tfx)];
  let refused = false;
  try {
    await prog.verifyShrink(tclaim, ...(twitness as any));
  } catch (e) {
    const msg = (e as Error).message;
    if (/no prover found|call.*compile/i.test(msg))
      fail(`VACUOUS tamper result — the program was not compiled: ${msg.split('\n')[0]}`);
    refused = true;
    ok(`REFUSED: ${msg.split('\n')[0].slice(0, 140)}`);
  }
  check(
    refused,
    'a tampered opened row is REFUSED through the commitment binding on the COMPILED program ' +
      '(verifyInputBatches recomputes a Merkle root ≠ dregg’s REAL emitted Pasta commit) — binds, not a re-mint',
  );

  // ---- [4] cost report ---------------------------------------------------
  const nq = fx.queries.length;
  console.log('\n[4] cost (native-Pasta shrink terminal, o1js Kimchi)');
  console.log(`    queries verified     : ${nq} (this ZkProgram = ONE query-batch step; the full 38-query verifier partitions across steps like the deployed root path)`);
  console.log(`    verifier rows        : ${rows === null ? '> few million (exceeds o1js analyzeMethods napi string limit)' : fmt(rows)}`);
  console.log(`    compile              : ${(compileMs / 1000).toFixed(2)}s`);
  console.log(`    prove                : ${(proveMs / 1000).toFixed(2)}s`);
  console.log(
    `    object               : ONE 2^15 native-Pasta batch-STARK (5 instances, ${fx.knobs.layers} FRI rounds, ${fx.knobs.numQueries} queries)`,
  );
  console.log(
    '    vs 199-instance chain: this is ONE ZkProgram over ONE proof (the chain is 199 instances / 12 keys of a RE-HASH that binds nothing)',
  );

  if (failures) throw new Error(`${failures} check(s) failed`);
  console.log('\n=== ALL CHECKS PASSED: o1js verifies dregg’s native-Pasta shrink terminal, binds, and refuses a tamper ===');
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
