import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Field } from 'o1js';
import { RealRootAir, rootAirDag, bindRealInstance, DagTable, RealInstance } from '../src/RootAirDag.js';
import {
  RealRootFri,
  airColumnIndex,
  friLaneTable,
  planOpenedValues,
  rootFriShape,
  rootPreambleMeta,
  segmentWalk,
} from '../src/RootFriWalk.js';
import {
  UniformSpec,
  assertHomogeneous,
  leafOf,
  planUniform,
  specName,
  totalSteps,
  uniformLaneTable,
  uniformLayout,
  vkTreeRoot,
} from '../src/RootFriUniform.js';
import { claimChunks, claimIndex, NUM_CHAIN_CLAIMS, SEG_ANCHOR_WIDTH, octetBigInt } from '../src/RootClaim.js';
import { assertRealPins, type DreggChainPins } from '../src/DreggHeadAnchor.js';

// ---------------------------------------------------------------------------
// THE PIN EMITTER — `dregg-chain-pins.json`, from the chain rather than by hand.
//
// `DreggHeadGate` bakes four constants into its verification key and refuses to
// exist without them. This is the ONE thing allowed to produce them.
//
// ⚑ IT REPRODUCES THE PLAN, IT DOES NOT RESTATE IT. Every call below is the one
// `root-claim-carry.ts`'s `context()` makes, in the same order, and the counts
// are cross-checked against that leg's own ratchet (905 instances, 131 programs)
// — so a plan that has drifted fails HERE rather than emitting a pin file for a
// chain nobody built.
//
// ⚑ AND THE KEYS IT READS MUST BE THE CLAIM-CARRYING ONES. `.fullchain/uniform`
// currently holds 46 keys from the §3.29-shape chain: `publicOutput: Field`, no
// claim, no preamble. §3.30 changed the public output type, so EVERY key in the
// chain changed; a pin file built from those 46 would name a chain whose terminal
// proof states nothing. This refuses a directory whose key count is not the
// program count and says which shape it found.
//
//   node dist/scripts/head-anchor-pins.js            # report only
//   node dist/scripts/head-anchor-pins.js --emit     # write the pin file
// ---------------------------------------------------------------------------

const WORK = process.env.HEAD_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const KEYS = process.env.HEAD_KEYS ?? resolve(WORK, 'uniform-claim');
const OUT = process.env.HEAD_PINS ?? resolve(process.cwd(), 'dregg-chain-pins.json');
const CHUNK = Number(process.env.CLAIM_CHUNK ?? 256);
const BUDGET = Number(process.env.CLAIM_BUDGET ?? 50_000);
const EMIT = process.argv.includes('--emit');

/** `root-claim-carry`'s ratchet, restated as a REFUSAL rather than a comment. */
const EXPECT = { instances: 905, programs: 131 };

const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};

function readReal(): { air: RealRootAir; fri: RealRootFri } {
  const a = resolve(WORK, 'real-root-air.json');
  const f = resolve(WORK, 'real-root-fri.json');
  if (!existsSync(a)) fail(`${a} is missing — run \`npm run root-air-fullchain\``);
  if (!existsSync(f)) fail(`${f} is missing — run the \`root_fri_instance\` dumper`);
  return { air: JSON.parse(readFileSync(a, 'utf8')), fri: JSON.parse(readFileSync(f, 'utf8')) };
}

function main() {
  const { air: realAir, fri: realFri } = readReal();
  const shape = rootFriShape(realFri);
  const airIx = airColumnIndex();
  const meta = rootPreambleMeta(realAir, airIx);
  const op = planOpenedValues(shape, airIx);
  //  ⚑ WITH the preamble — 905 / 131 is the §3.29 shape and 820 / 46 is the one
  //  without it. Getting this wrong changes `totalSteps`, which is a PIN.
  const w = segmentWalk(shape, { preamble: meta });
  const ftD = friLaneTable(shape, op);
  const L = uniformLayout(w, shape, ftD, CHUNK);
  const ft = uniformLaneTable(shape, ftD, L);
  assertHomogeneous(w, op, ft, L);
  const plan = planUniform(w, op, ft, L, { usableRows: BUDGET });

  const programs: UniformSpec[] = [
    ...plan.head.map((_, pos) => ({ kind: 'head' as const, pos })),
    ...plan.block.map((_, pos) => ({ kind: 'block' as const, pos })),
  ];
  const terminal: UniformSpec = { kind: 'block', pos: plan.block.length - 1 };
  const T = totalSteps(plan);

  console.log('=== HEAD-ANCHOR PINS ===\n');
  console.log(`    instances     ${plan.totalSlices} uniform + 7 AIR = ${T} steps  (totalSteps PIN)`);
  console.log(`    programs      ${programs.length}  (${plan.head.length} head + ${plan.block.length} block)`);
  console.log(`    terminal      ${specName(terminal)} at key-tree leaf ${leafOf(plan, terminal)}`);

  if (plan.totalSlices !== EXPECT.instances || programs.length !== EXPECT.programs)
    fail(
      `the plan is ${plan.totalSlices} instances / ${programs.length} programs and ` +
        `root-claim-carry's ratchet pins ${EXPECT.instances} / ${EXPECT.programs}. The plan moved; ` +
        'a pin file emitted from it would name a chain that leg never measured.',
    );
  console.log(`    ✓ matches root-claim-carry's ratchet (${EXPECT.instances} / ${EXPECT.programs})`);

  //  The claim's own geometry, so a pin file cannot be emitted for a chain whose
  //  claim does not resolve.
  const ix = claimIndex(airIx);
  const chunks = claimChunks(ix, CHUNK);
  console.log(`    claim         ${NUM_CHAIN_CLAIMS} lanes, AIR chunks [${chunks}]`);

  //  The genesis anchor, off the proof's own `expose_claim` public values.
  const ec = realAir.instances.find((i: any) => (i as any).table === 'expose_claim') as any;
  if (!ec) fail('the root proof exposes no claim — there is no genesis anchor to pin');
  const lanes: bigint[] = ec.publicValues.map((x: any) => BigInt(x));
  const genesisRoot = octetBigInt(lanes.slice(0, SEG_ANCHOR_WIDTH));
  console.log(`    genesisRoot   0x${genesisRoot.toString(16)}`);

  //  ---- the keys ---------------------------------------------------------
  const keyFile = (sp: UniformSpec) => resolve(KEYS, `key-${specName(sp)}.json`);
  const missing = programs.filter((sp) => !existsSync(keyFile(sp)));
  if (missing.length) {
    console.log(`\n    ◌ NOT EMITTABLE — ${missing.length} of ${programs.length} keys are absent in ${KEYS}`);
    console.log(`      first missing: ${missing.slice(0, 4).map(specName).join(', ')}`);
    console.log(
      '      ⚑ AND `.fullchain/uniform` IS NOT THE ANSWER. Those 46 keys are the §3.29 chain:\n' +
        '        `publicOutput: Field`, no claim, no preamble. §3.30 changed the public output\n' +
        '        type, so every key in the chain changed. The claim-carrying chain must be\n' +
        '        compiled — 131 programs, one process each — into HEAD_KEYS.',
    );
    if (EMIT) fail('--emit was given and the key list is incomplete. There is no partial pin file.');
    return;
  }

  const hashes = programs.map((sp) => Field(JSON.parse(readFileSync(keyFile(sp), 'utf8')).hash));
  const root = vkTreeRoot(hashes);
  const terminalHash = hashes[leafOf(plan, terminal)];

  const pins: DreggChainPins = assertRealPins({
    label: `dregg root-fri uniform chain, claim-carrying, ${programs.length} programs / ${T} steps`,
    terminalVkHash: terminalHash.toBigInt(),
    chainVkRoot: root.toBigInt(),
    totalSteps: T,
    genesisRoot,
  });
  console.log(`\n    terminalVkHash ${pins.terminalVkHash}`);
  console.log(`    chainVkRoot    ${pins.chainVkRoot}`);

  if (!EMIT) {
    console.log('\n    (report only — pass `--emit` to write the pin file)\n');
    return;
  }
  writeFileSync(
    OUT,
    JSON.stringify(
      {
        ...pins,
        terminalVkHash: pins.terminalVkHash.toString(),
        chainVkRoot: pins.chainVkRoot.toString(),
        genesisRoot: pins.genesisRoot.toString(),
        terminalProgram: specName(terminal),
        terminalLeaf: leafOf(plan, terminal),
        emittedAt: new Date().toISOString(),
        keys: KEYS,
      },
      null,
      2,
    ) + '\n',
  );
  console.log(`\n    wrote ${OUT}\n`);
}

main();
