import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Bool, Cache, Field } from 'o1js';
import { shrinkShapeOf, shrinkValues } from '../src/MinaShrinkVerify.js';
import { rootClaim, rootWitness } from '../src/RootConsume.js';
import { makeMinaShrinkPartition, claimTraceOffset } from '../src/MinaShrinkPartition.js';
import { entryBoundaryOf } from '../src/DreggProofPartition.js';
import { EXT_D } from '../src/FriQueryStep.js';
import { NUM_CHAIN_CLAIMS } from '../src/RootClaim.js';

// ---------------------------------------------------------------------------
// THE FULL SHRINK PARTITION — o1js verifies EVERY query of dregg's native-Pasta
// shrink terminal, one query per Pickles step, carrying the SEALED G→H
// ChainClaim, and closing into a terminal a head gate consumes.
//
//   [0] out-of-circuit differential: the claim read from `openedTrace` at the
//       computed offset equals the fixture's `claimLanes` (offset is right);
//   [1] compile step0 + walk (Cache.None, measured — key count + per-key time);
//   [2] prove step0 → walk.first → walk.step × … (measured per-step), up to
//       MINA_PART_STEPS walk steps (default all 38); the true last query emits
//       the terminal seal;
//   [3] save the terminal proof + pins to .fullchain/uniform-claim-shrink/.
//
//   MINA_SHRINK_FIXTURE=… MINA_PART_STEPS=38 O1JS_BACKEND=native npm run mina-shrink-partition
// ---------------------------------------------------------------------------

const fmt = (n: number) => Math.round(n).toLocaleString('en-US');
const secs = (ms: number) => (ms / 1000).toFixed(2) + 's';
let failures = 0;
const ok = (m: string) => console.log('  ✓ ' + m);
const fail = (m: string): never => {
  failures++;
  console.error('  ✗ ' + m);
  throw new Error(m);
};
const check = (c: boolean, m: string) => (c ? ok(m) : fail(m));

const WORK = resolve(process.cwd(), '.fullchain', 'uniform-claim-shrink');

function loadFixture(): any {
  const p =
    process.env.MINA_SHRINK_FIXTURE ??
    resolve(process.cwd(), '.fullchain', 'mina-shrink-fixture.json');
  if (!existsSync(p)) throw new Error(`shrink fixture absent at ${p}`);
  return JSON.parse(readFileSync(p, 'utf8'));
}

async function main() {
  console.log('=== THE FULL SHRINK PARTITION — o1js verifies all 38 queries + seals the claim ===\n');
  mkdirSync(WORK, { recursive: true });

  const fx = loadFixture();
  const claimInstance = fx.claimInstance as number;
  console.log(
    `fixture: kind=${fx.kind} instances=${fx.degreeBits.length} queries=${fx.knobs.numQueries} ` +
      `rounds=${fx.knobs.layers} log_gmh=${fx.knobs.logGlobalMaxHeight} claimInstance=${claimInstance}\n`,
  );

  const sh = shrinkShapeOf(fx);
  const v = shrinkValues(fx);
  const part = makeMinaShrinkPartition(sh, claimInstance);
  const { step0, walk, nSteps, numQueries } = part;

  // ---- [0] OUT-OF-CIRCUIT DIFFERENTIAL: the claim-seal offset is right -------
  console.log('[0] claim-seal differential (out of circuit)');
  const off = claimTraceOffset(sh, claimInstance);
  const claimLanes = (fx.claimLanes as number[]).slice(0, NUM_CHAIN_CLAIMS).map((x) => BigInt(x));
  // v.opened[0][claimInstance][0] is the flat base lanes of the claim matrix pt0.
  //  pt0 is flat: numCols columns × EXT_D lanes each. Lane i lives at column
  //  EXT_D·i, whose base is flat index (EXT_D·i)·EXT_D — the same value the
  //  module reads as `openedTrace[off + EXT_D·i].limbs[0]` (openedTrace being one
  //  BbExt per column).
  const pt0 = v.opened[0][claimInstance][0] as unknown as Array<number | bigint>;
  const readFromMatrix = Array.from({ length: NUM_CHAIN_CLAIMS }, (_, i) =>
    BigInt(pt0[EXT_D * i * EXT_D]),
  );
  const flatOk = claimLanes.every((x, i) => x === readFromMatrix[i]);
  check(
    flatOk,
    `claim read at column stride ${EXT_D} == fixture claimLanes[0..${NUM_CHAIN_CLAIMS - 1}] ` +
      `(genesis lane0=${claimLanes[0]}, numTurns lane16=${claimLanes[16]})`,
  );
  console.log(`    claimTraceOffset in flat openedTrace = ${off}, nSteps = ${nSteps}\n`);
  if (process.env.MINA_PART_PHASE === 'diff') {
    ok('diff-only phase: partition constructed, claim-seal offset validated');
    if (failures) throw new Error(`${failures} check(s) failed`);
    return;
  }

  // ---- witness plumbing ------------------------------------------------------
  const Claim = part.Claim;
  const claim = rootClaim(sh, v, Claim);
  const full = rootWitness(sh, v); // [oT,oQ,qpw,rows(38),ip(38),sib(38),cp(38),aA,z,fA,betas,qb(38)]
  const [oT, oQ, qpw, rowsAll, ipAll, sibAll, cpAll, aA, z, fA, betas, qbAll] = full;
  const proofGlobal = [claim, oT, oQ, qpw, aA, z, fA, betas, qbAll];
  const walkTailFor = (g: number) => [[rowsAll[g]], [ipAll[g]], [sibAll[g]], [cpAll[g]]];

  // ---- [1] COMPILE step0 + walk (Cache.None, measured) -----------------------
  console.log('[1] compile (Cache.None)');
  const keyTimes: Record<string, number> = {};
  let t = performance.now();
  const { verificationKey: vk0 } = await step0.compile({ cache: Cache.None });
  keyTimes.step0 = performance.now() - t;
  ok(`step0 VK compiled: hash=${vk0.hash.toString().slice(0, 18)}…  ${secs(keyTimes.step0)}`);

  //  Fast step0-only iteration: compile + prove step0 alone (skip the ~220s walk
  //  compile) to settle chunk/wrap config.
  if (process.env.MINA_PART_PHASE === 'step0') {
    const entry0 = entryBoundaryOf(claim as any, oT, oQ, qpw, true);
    const tp = performance.now();
    const s0 = await step0.transcript(entry0.boundary, ...(proofGlobal as any));
    check(await step0.verify(s0.proof), `step0 proved + verified (${secs(performance.now() - tp)})`);
    const c = s0.proof.publicOutput.claim;
    console.log(
      `    sealed claim: genesis=${c.genesisRoot.toString().slice(0, 14)}… final=${c.finalRoot
        .toString()
        .slice(0, 14)}… numTurns=${c.numTurns.toString()}`,
    );
    if (failures) throw new Error(`${failures} check(s) failed`);
    return;
  }
  t = performance.now();
  const { verificationKey: vkW } = await walk.compile({ cache: Cache.None });
  keyTimes.walk = performance.now() - t;
  ok(`walk  VK compiled: hash=${vkW.hash.toString().slice(0, 18)}…  ${secs(keyTimes.walk)}`);
  console.log(
    `    ⇒ ${Object.keys(keyTimes).length} distinct VKs, ` +
      `${secs(keyTimes.step0 + keyTimes.walk)} total compile\n`,
  );

  // ---- [2] PROVE the chain (measured per-step) -------------------------------
  const maxWalk = Number(process.env.MINA_PART_STEPS ?? numQueries);
  console.log(`[2] prove: step0 + ${Math.min(maxWalk, numQueries)} walk steps (of ${numQueries})`);

  const bStart = performance.now();
  const entry = entryBoundaryOf(claim as any, oT, oQ, qpw, true);
  const b0 = entry.boundary;

  t = performance.now();
  const s0 = await step0.transcript(b0, ...(proofGlobal as any));
  const s0ms = performance.now() - t;
  check(await step0.verify(s0.proof), `step0 proved + verified (${secs(s0ms)})`);
  let prev = s0.proof;
  const stepMs: number[] = [s0ms];

  let g = 0; // walk.first walks global query 0
  const isLastAt = (k: number) => k === numQueries;
  // walk.first (k=1)
  if (maxWalk >= 1) {
    t = performance.now();
    const bIn = prev.publicOutput.boundary;
    const w1 = await walk.first(bIn, prev as any, Bool(isLastAt(1)), ...(walkTailFor(0) as any));
    const w1ms = performance.now() - t;
    check(await walk.verify(w1.proof), `walk.first (k=1, query 0) proved + verified (${secs(w1ms)})`);
    stepMs.push(w1ms);
    prev = w1.proof;
  }
  // walk.step (k = 2 .. maxWalk)
  for (let k = 2; k <= Math.min(maxWalk, numQueries); k++) {
    g = k - 1;
    t = performance.now();
    const bIn = prev.publicOutput.boundary;
    const wk = await walk.step(
      bIn,
      prev as any,
      Field(k),
      Bool(isLastAt(k)),
      ...(walkTailFor(g) as any),
    );
    const wkms = performance.now() - t;
    check(
      await walk.verify(wk.proof),
      `walk.step k=${k} (query ${g})${isLastAt(k) ? ' [LAST → terminal seal]' : ''} proved + verified (${secs(wkms)})`,
    );
    stepMs.push(wkms);
    prev = wk.proof;
  }
  const proveTotal = performance.now() - bStart;

  const provedWalk = Math.min(maxWalk, numQueries);
  const reachedTerminal = provedWalk === numQueries;
  console.log(
    `\n    per-step prove (s): [${stepMs.map((m) => (m / 1000).toFixed(1)).join(', ')}]`,
  );
  const avg = stepMs.slice(1).reduce((a, b) => a + b, 0) / Math.max(stepMs.length - 1, 1);
  console.log(
    `    step0 ${secs(stepMs[0])}; avg walk ${secs(avg)}; ${stepMs.length} steps proved in ` +
      `${secs(proveTotal)} (measured, not extrapolated)`,
  );

  // ---- [3] SAVE terminal + pins ----------------------------------------------
  const claimOut = prev.publicOutput.claim;
  console.log('\n    exposed G→H ChainClaim (public output of the chain so far):');
  console.log(`      genesisRoot : ${claimOut.genesisRoot.toString()}`);
  console.log(`      finalRoot   : ${claimOut.finalRoot.toString()}`);
  console.log(`      numTurns    : ${claimOut.numTurns.toString()}`);
  console.log(`      chainDigest : ${claimOut.chainDigest.toString()}`);

  const rcd = entry.rcd;
  const pins = {
    label: `mina-shrink-partition/${fx.vkFingerprint}/q${numQueries}`,
    terminalVkHash: vkW.hash.toBigInt().toString(),
    totalSteps: nSteps,
    genesisRoot: claimOut.genesisRoot.toBigInt().toString(),
    rootCommitDigest: rcd.toBigInt().toString(),
    numTurns: Number(claimOut.numTurns.toBigInt()),
    finalRoot: claimOut.finalRoot.toBigInt().toString(),
    chainDigest: claimOut.chainDigest.toBigInt().toString(),
    step0VkHash: vk0.hash.toBigInt().toString(),
    reachedTerminal,
    provedWalkSteps: provedWalk,
  };
  writeFileSync(resolve(WORK, 'shrink-partition-pins.json'), JSON.stringify(pins, null, 2));
  if (reachedTerminal) {
    writeFileSync(
      resolve(WORK, 'shrink-terminal-proof.json'),
      JSON.stringify(prev.toJSON()),
    );
    // ── ⚑ THE TRACKED MIRROR — the half that was missing, and why it is here ────────────────
    // `WORK` is `.fullchain/uniform-claim-shrink/`, and `.fullchain/` IS GITIGNORED. So until
    // 2026-08-06 the ONLY copy of this pin lived in a directory no clone carries and no clone can
    // produce without 39 Pickles proves over a fixture it also does not have. Measured that day:
    // the directory did not exist at all, so `DreggShrinkHeadGate`'s terminal key resolved to
    // ABSENT everywhere, and the `vk-identity` leg that is supposed to cross-check it was
    // comparing against nothing while printing a clean sweep.
    //
    // The RootFriUniform chains already had the answer beside them: `dregg-chain-pins.json` is a
    // TRACKED mirror of a gitignored key ring, read as `mirror-only` and labelled UNCHECKED on any
    // box that did not compile the chain. This is that file for the shrink family. It is written
    // ONLY on a terminal run — a partial walk must never mint a tracked pin naming a mid-chain
    // step as a terminal, which is the one way this artifact could lie.
    const MIRROR = resolve(process.cwd(), 'dregg-shrink-pins.json');
    writeFileSync(
      MIRROR,
      JSON.stringify(
        {
          _: 'TRACKED MIRROR of .fullchain/uniform-claim-shrink/shrink-partition-pins.json. ' +
            'Emitted by scripts/mina-shrink-partition.ts on a TERMINAL run only. Consumed by ' +
            'DreggShrinkHeadGate (src/DreggShrinkHead.ts) and cross-checked by `npm run ' +
            'vk-identity`, which reads the ring when it is present and reds if the two disagree. ' +
            'Regenerate: npm run mina-shrink-partition. Do not hand-edit.',
          label: pins.label,
          terminalVkHash: pins.terminalVkHash,
          totalSteps: pins.totalSteps,
          genesisRoot: pins.genesisRoot,
          step0VkHash: pins.step0VkHash,
        },
        null,
        2,
      ) + '\n',
    );
    ok(`TERMINAL reached (all ${numQueries} queries) — proof + pins saved to ${WORK}`);
    ok(`tracked mirror written to ${MIRROR} — COMMIT IT; it is the only copy a clone can read`);
  } else {
    console.log(
      `\n  ⚑ PARTIAL: proved step0 + ${provedWalk}/${numQueries} walk steps (MINA_PART_STEPS). ` +
        `The remaining ${numQueries - provedWalk} walk steps are the outstanding compute; ` +
        `per-step is measured above. Pins saved (reachedTerminal=false).`,
    );
  }

  if (failures) throw new Error(`${failures} check(s) failed`);
  console.log('\n=== partition run complete ===');
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
