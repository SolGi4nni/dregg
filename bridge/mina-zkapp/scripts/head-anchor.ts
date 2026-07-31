import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  AccountUpdate,
  Field,
  Mina,
  Poseidon,
  PrivateKey,
  SelfProof,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import { ChainClaim, ClaimedBoundary } from '../src/RootClaim.js';
import { airTerminalSeal, digestOfLanes, stepBoundary } from '../src/RootAirChain.js';
import {
  ClaimValues,
  DreggBootstrap,
  DreggChainPins,
  DreggTerminalProof,
  HeadState,
  __resetHeadGateFactoryForTest,
  advanceBigInt,
  assertRealPins,
  bootstrapHistory,
  bootstrapProvenance,
  canonicalBootstrapState,
  claimFieldsOf,
  decideBigInt,
  forkWitnessOf,
  historyLink,
  makeDreggHeadGate,
  terminalSealOf,
} from '../src/DreggHeadAnchor.js';
import { MINA_TIER, atTier, tierStop } from '../src/tier.js';

// ---------------------------------------------------------------------------
// LEG 22 — THE ANCHOR STOPS BEING SIGNED.
//
// `DreggAttestedGate.setDreggRoot(anchor, placeholderAuth)` anchors a root
// because a named key signed the transition; its own header says the proof
// obligation is a SHAPE constraint and the key is "the ONLY thing that currently
// makes the anchor unforgeable". `DreggHeadGate` replaces the signature with the
// terminal proof of dregg's own root-proof verification chain, whose public
// output has STATED `(G, H, N, D)` since §3.30.
//
// ⚑ THREE-VALUED, AND THE THIRD VALUE IS THE HONEST ONE. Every row is REFUSED,
// ACCEPTED or NOT ATTRIBUTABLE WITH A REASON. The row that matters most —
// "dregg's REAL terminal proof is accepted" — is NOT ATTRIBUTABLE today and says
// why: the chain has not been compiled to a key list or proved to a terminal
// proof, so `dregg-chain-pins.json` does not exist and there is nothing to hand
// the gate. Printing that as a skip, or leaving it out, would be the shape this
// tree keeps paying for.
//
// ⚑ AND THE FALSIFIERS LIVE WHERE THE ASSERTIONS DO. The vk pin, the terminal-
// seal exhibition, the extension check, the halt and the fork predicate are all
// assertions inside `DreggHeadGate`, and every refusal below is produced against
// that circuit with a real `prove()`. The STAND-IN producer is not dregg's chain
// and is never described as one: what it makes attributable is the GATE's
// assertions, which is exactly what it is pointed at.
//
// ⚑ WHY A STAND-IN IS NOT A SMALLER RUN OF THE SAME TEST. The trap named in this
// arc is a test that chooses its own subject from what the run happened to do.
// Here the subject is fixed by the harness: the stand-in emits a boundary and a
// claim the ROW specifies, so each row targets one named assertion and the
// object it is fed is not a function of what compiled.
//
//   MINA_TIER=0   the out-of-circuit table. Nothing compiles. Seconds.
//   MINA_TIER=1   + the LocalBlockchain table against a real prove(), the
//                 UNPINNED control, and the vk-facts phase.
//   MINA_TIER=2   + nothing yet: the real chain is a coordinator job and the
//                 row for it is printed NOT ATTRIBUTABLE at every tier.
//
// ⚑ THE VK-PIN ROW WAS A GREEN OVER A FALSE PREMISE UNTIL 2026-07-30, and the
// repair is the `standIn` factory below plus `assertDistinctKeys`. Both stand-in
// producers used to differ ONLY in their `name:`, and a Kimchi verification key
// does not commit to a program's name — so the row aimed at `vk.hash
// .assertEquals` compared two EQUAL fields and passed whatever the pin did, and
// so did the UNPINNED control that is supposed to make its refusal attributable.
// The accept row meanwhile could not run at all: the stand-in had no proof input
// and therefore `maxProofsVerified = 0`, while `DreggTerminalProof` declares 1,
// so every advance died at Pickles' `prevs_verified` before reaching this gate.
// Both are fixed HERE, in the harness, and neither was a defect in
// `DreggHeadGate`. What enters a verification key is written out below the
// out-of-circuit table and MEASURED by phase [4].
// ---------------------------------------------------------------------------

const WORK = process.env.HEAD_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const PHASE = process.env.HEAD_PHASE ?? 'main';
const PINS_PATH = process.env.HEAD_PINS ?? resolve(process.cwd(), 'dregg-chain-pins.json');

let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};
const na = (what: string, why: string) => {
  console.log(`  ◌ NOT ATTRIBUTABLE — ${what}`);
  console.log(`      reason: ${why}`);
};
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;
const hex = (x: bigint) => `0x${x.toString(16).slice(0, 16)}…`;

/** ⚑ EVERY CAUGHT ERROR MUST BE A CONSTRAINT FAILURE. §3.28's rule, kept
 *  verbatim because §3.29's first run "refused" on the bound side and DIED on
 *  the control side, both from a witness-builder bug — a `TypeError` inside a
 *  bare `catch {}` is indistinguishable from a refusal. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|Bool\.assertTrue|DreggHeadGate/i.test(
    m,
  );
}

// ===========================================================================
// The real claim, off dregg's committed root proof.
//
// ⚑ READ, NOT RE-RESOLVED. `root-claim-carry` (leg 21) is what proves that the
// 25 `expose_claim` lanes are the claim, against three independent oracles and
// eight discriminating polarities. Re-deriving the legend here would be a second
// answer to a settled question; this leg reads the instance's own
// `public_values` and re-checks the ONE oracle that sits outside the column
// assignment (`numTurns`), so a swapped artifact is still caught.
// ===========================================================================

const SEG_ANCHOR_WIDTH = 8;
const octet = (l: bigint[]) => l.reduce((a, v, j) => a + v * (1n << (31n * BigInt(j))), 0n);

function realClaim(): { claim: ClaimValues; numTurnsOracle: number } {
  const p = resolve(WORK, 'real-root-air.json');
  if (!existsSync(p))
    fail(`${p} is missing — run \`npm run root-air-fullchain\`. A missing artifact is a FAILURE, not a skip.`);
  const j = JSON.parse(readFileSync(p, 'utf8'));
  const ec = (j.instances ?? []).find((i: any) => i.table === 'expose_claim');
  if (!ec) fail('the root proof carries no `expose_claim` instance — there is no claim to anchor');
  const L: bigint[] = ec.publicValues.map((x: any) => BigInt(x));
  if (L.length !== 25) fail(`a claim is 25 lanes and this proof exposes ${L.length}`);
  if (typeof j.numTurns !== 'number')
    fail('the artifact records no top-level `numTurns` — the decode has no oracle outside itself');
  return {
    claim: {
      genesisRoot: octet(L.slice(0, SEG_ANCHOR_WIDTH)),
      finalRoot: octet(L.slice(SEG_ANCHOR_WIDTH, 2 * SEG_ANCHOR_WIDTH)),
      numTurns: L[2 * SEG_ANCHOR_WIDTH],
      chainDigest: octet(L.slice(2 * SEG_ANCHOR_WIDTH + 1, 2 * SEG_ANCHOR_WIDTH + 1 + 8)),
    },
    numTurnsOracle: j.numTurns,
  };
}

/** The pins, if a real chain compile has emitted them. Absent is the expected
 *  state today and is reported as such — never defaulted. */
function realPins(): DreggChainPins | null {
  if (!existsSync(PINS_PATH)) return null;
  const j = JSON.parse(readFileSync(PINS_PATH, 'utf8'));
  return assertRealPins({
    label: j.label,
    terminalVkHash: BigInt(j.terminalVkHash),
    chainVkRoot: BigInt(j.chainVkRoot),
    totalSteps: Number(j.totalSteps),
    genesisRoot: BigInt(j.genesisRoot),
  });
}

// ===========================================================================
// [1] THE OUT-OF-CIRCUIT TABLE — nothing compiles.
// ===========================================================================

function differential() {
  console.log('\n[1] THE HEAD, OUT OF CIRCUIT — the decision, the seal and the bootstrap\n');

  const { claim: C, numTurnsOracle } = realClaim();
  if (C.numTurns !== BigInt(numTurnsOracle))
    fail(`the claim decodes numTurns = ${C.numTurns} and the artifact records ${numTurnsOracle}`);
  ok(`the committed root proof's claim decodes, and \`numTurns\` = ${C.numTurns} matches the artifact's own`);
  console.log(`    G ${hex(C.genesisRoot)}   H ${hex(C.finalRoot)}   N ${C.numTurns}   D ${hex(C.chainDigest)}`);

  // -- the seal exhibition, and what each pin in it moves ------------------
  const fc = Field(11111n);
  const aod = Field(22222n);
  const R = Field(33333n);
  const T = 912;
  const seal = terminalSealOf(fc, aod, R, T);
  if (seal.toBigInt() !== airTerminalSeal(fc, Poseidon.hash([aod, R]), Field(T)).toBigInt())
    fail('`terminalSealOf` is not the chain\'s own `airTerminalSeal` over its own `terminalDigest`');
  ok('the seal a caller exhibits is the chain\'s OWN `airTerminalSeal` — one definition, not two');

  const moves: [string, Field][] = [
    ['friCommit', terminalSealOf(Field(11112n), aod, R, T)],
    ['accOutDigest', terminalSealOf(fc, Field(22223n), R, T)],
    ['chainVkRoot', terminalSealOf(fc, aod, Field(33334n), T)],
    ['totalSteps', terminalSealOf(fc, aod, R, T - 1)],
  ];
  for (const [name, v] of moves)
    if (v.toBigInt() === seal.toBigInt())
      fail(`the seal does not move when \`${name}\` does — that pin does not bite`);
  ok('all FOUR preimage slots move the seal — the key-list root and the chain LENGTH both bite');

  // ⚑ THE DOMAIN SEPARATION, EXHIBITED NUMERICALLY RATHER THAN ASSERTED. The
  // last block position emits `Provable.if(isQ[Q-1], seal, step)`, so a
  // mid-chain proof of the SAME program carries a `stepBoundary`. If a step
  // boundary were exhibitable as a seal the gate would accept a chain that
  // walked six of nineteen queries.
  let clash = 0;
  for (let k = T - 40; k <= T + 40; k++)
    for (const carried of [Field(0), aod, Poseidon.hash([aod, R])])
      if (stepBoundary(fc, carried, Field(k)).toBigInt() === seal.toBigInt()) clash++;
  if (clash !== 0) fail(`${clash} step boundaries collide with the terminal seal at the same commitment`);
  ok('no step boundary in a ±40-step window collides with the seal (4-field tagged vs 3-field)');

  // -- the decision ---------------------------------------------------------
  const G = C.genesisRoot;
  const s0: HeadState = { ...canonicalStateBig(G) };
  if (decideBigInt(s0, C).verdict !== 'advance')
    fail(`the REAL claim is not an advance from the pinned genesis: ${decideBigInt(s0, C).why}`);
  ok('the committed root proof IS a valid first advance from its own genesis anchor');

  const s1 = advanceBigInt(s0, C);
  if (s1.head !== C.finalRoot || s1.turns !== C.numTurns || s1.prevHead !== G)
    fail('the advance did not move head/turns/prevHead the way it says it does');
  ok(`after it: head = H, turns = ${s1.turns}, prevHead = G`);

  const seg2: ClaimValues = { genesisRoot: C.finalRoot, finalRoot: 777n, numTurns: 5n, chainDigest: 888n };
  const s2 = advanceBigInt(s1, seg2);
  ok(`a second segment extends it: turns = ${s2.turns} = ${C.numTurns} + 5`);

  //  ⚑ THE FORK PREDICATE, AND THE THREE THINGS IT MUST NOT FIRE ON.
  const rows: [string, ClaimValues, HeadState, string][] = [
    [
      'same start, same length, a different end',
      { genesisRoot: C.finalRoot, finalRoot: 999n, numTurns: 5n, chainDigest: 1000n },
      s2,
      'fork',
    ],
    [
      'same start, a DIFFERENT length — an honest prefix, not an equivocation',
      { genesisRoot: C.finalRoot, finalRoot: 999n, numTurns: 2n, chainDigest: 1000n },
      s2,
      'stale',
    ],
    ['the segment already accepted, re-presented', seg2, s2, 'stale'],
    [
      'a segment from a state this client never held',
      { genesisRoot: 4242n, finalRoot: 999n, numTurns: 5n, chainDigest: 1000n },
      s2,
      'stale',
    ],
    [
      'an honest first segment CANNOT halt a fresh client',
      { genesisRoot: G, finalRoot: 999n, numTurns: 5n, chainDigest: 1000n },
      s0,
      'advance',
    ],
    ['a zero-turn segment', { genesisRoot: C.finalRoot, finalRoot: 999n, numTurns: 0n, chainDigest: 1n }, s2, 'stale'],
    ['anything at all, once halted', seg2, { ...s2, fork: 1n }, 'halted'],
  ];
  for (const [what, cv, st, want] of rows) {
    const got = decideBigInt(st, cv);
    if (got.verdict !== want)
      fail(`'${what}' decides '${got.verdict}' and must decide '${want}' (${got.why})`);
    console.log(`      ${want.padEnd(7)}  ${what}`);
  }
  ok(`the decision is four-valued on ${rows.length} rows, and a PREFIX is not a fork`);

  // -- the history link is a real chain, not a set -------------------------
  const h1 = historyLink(Field(0), claimFieldsOf(C));
  const h2 = historyLink(h1, claimFieldsOf(seg2));
  const swapped = historyLink(historyLink(Field(0), claimFieldsOf(seg2)), claimFieldsOf(C));
  if (h2.toBigInt() === swapped.toBigInt()) fail('the accepted-history fold is order-blind');
  if (forkWitnessOf(claimFieldsOf(C)).toBigInt() === h1.toBigInt())
    fail('a fork witness and a history link share an image — the domain tags do not separate');
  ok('the accepted-history fold is ORDER-SENSITIVE and domain-separated from a fork witness');

  // -- the pins refuse to be typed by hand ---------------------------------
  const good: DreggChainPins = {
    label: 'stand-in (leg 22)',
    terminalVkHash: 1n,
    chainVkRoot: 2n,
    totalSteps: 3,
    genesisRoot: G,
  };
  assertRealPins(good);
  const holes: [string, DreggChainPins][] = [
    ['no label', { ...good, label: '' }],
    ['terminalVkHash = 0', { ...good, terminalVkHash: 0n }],
    ['chainVkRoot = 0', { ...good, chainVkRoot: 0n }],
    ['totalSteps = 0', { ...good, totalSteps: 0 }],
    ['genesisRoot = 0', { ...good, genesisRoot: 0n }],
  ];
  for (const [what, p] of holes) {
    let accepted = false;
    try {
      assertRealPins(p);
      accepted = true;
    } catch {
      /* expected */
    }
    if (accepted) fail(`\`assertRealPins\` accepted a pin file with ${what}`);
  }
  ok(`\`assertRealPins\` refuses all ${holes.length} placeholder shapes and accepts a measured one`);

  // -- the bootstrap is named, typed and readable back ---------------------
  let bad = false;
  try {
    DreggBootstrap.weakSubjectivityAnchor(Field(0), 'a perfectly long attestation string');
    bad = true;
  } catch {
    /* expected */
  }
  try {
    DreggBootstrap.weakSubjectivityAnchor(Field(G), 'short');
    bad = true;
  } catch {
    /* expected */
  }
  if (bad) fail('`weakSubjectivityAnchor` accepted a zero genesis or an unattested one');
  const anchor = DreggBootstrap.weakSubjectivityAnchor(
    Field(G),
    'leg 22: the committed root proof\'s own genesis anchor',
  );
  if (anchor.provenance !== 'weak-subjectivity-anchor')
    fail('the bootstrap does not carry its provenance');
  ok('the bootstrap has ONE named constructor, refuses a zero anchor and carries its provenance');

  const canon = canonicalBootstrapState(good);
  const seen = {
    head: canon.head,
    prevHead: canon.prevHead,
    turns: canon.turns,
    acceptedHistory: canon.acceptedHistory,
    fork: canon.fork,
  };
  const provRows: [string, any, 'genesis' | 'operator-asserted-head' | 'halted'][] = [
    ['the canonical bootstrap', seen, 'genesis'],
    ['a deployer-asserted later head', { ...seen, turns: Field(9), head: Field(4242) }, 'operator-asserted-head'],
    ['a halted client', { ...seen, fork: Field(7) }, 'halted'],
  ];
  for (const [what, st, want] of provRows) {
    const v = bootstrapProvenance(st, good).verdict;
    if (v !== want) fail(`'${what}' reads back as '${v}' and must read '${want}'`);
    console.log(`      ${want.padEnd(22)}  ${what}`);
  }
  ok('`bootstrapProvenance` is three-valued on a deployed account — halted is not a bad deploy');

  return { C, G };
}

const canonicalStateBig = (g: bigint): HeadState => ({
  head: g,
  prevHead: g,
  turns: 0n,
  lastSegmentTurns: 0n,
  acceptedHistory: bootstrapHistory(Field(g)).toBigInt(),
  fork: 0n,
});

// ===========================================================================
// [2] THE CIRCUIT TABLE — one gate compile, a real prove() per row.
// ===========================================================================

// ---------------------------------------------------------------------------
// ⚑ WHAT ENTERS A KIMCHI/PICKLES VERIFICATION KEY, AND WHAT DOES NOT.
//
// Written here because it surprised a careful lane, and the thing it surprised
// them into was a GREEN OVER A FALSE PREMISE: two `ZkProgram`s differing only in
// their `name:` field compiled to the SAME `vk.hash`, so the row aimed at this
// gate's vk pin compared two EQUAL fields and passed no matter what the pin did.
// The `vkfacts` phase below MEASURES each line of this; none of it is asserted.
//
//   ENTERS — because the key commits to the CONSTRAINT SYSTEM and to the branch
//   structure Pickles wraps it in:
//     * the gates: every constraint, and therefore every `Poseidon.hash`,
//       `assert*`, range check and lookup a method emits, plus the domain size
//       they round up to;
//     * the WIRING: the permutation argument's sigma commitments, i.e. which
//       cells are equated with which;
//     * the number of public input/output FIELD ELEMENTS (the layout, not the
//       provable type's name);
//     * `maxProofsVerified` and the METHOD COUNT — Pickles builds one branch per
//       method and the branch table is inside the wrap key. This is why a
//       stand-in without a proof input is not merely "smaller": it is a
//       DIFFERENT SHAPE, and side-loading it into a `DynamicProof` that declares
//       `maxProofsVerified = 1` dies at `prevs_verified` before any assertion in
//       this gate is reached;
//     * the feature flags the circuit was compiled with.
//
//   DOES NOT ENTER — o1js bookkeeping, used to key the prover-key cache and to
//   name the class, never turned into a polynomial commitment:
//     * `name:` — the program's name;
//     * the method's own identifier, beyond its position in the branch table;
//     * the TypeScript identifiers of the provable types.
//
// So "a proof of a DIFFERENT program" is only a real row if the two programs
// have DIFFERENT CONSTRAINT SYSTEMS. `standIn`'s `extraRounds` is what supplies
// that, and it is not decoration — with it at 0 for both producers, the vk pin
// below is untestable and the UNPINNED control in §[3] is untestable with it.
// ---------------------------------------------------------------------------

/**
 * ⚑ THE MAXIMALLY ADVERSARIAL STAND-IN. It emits ANY boundary and ANY claim,
 * because a stand-in that could only emit honest values would make the gate's
 * refusals unfalsifiable. What it stands in for is the chain's TYPE — public
 * input `Field`, public output `ClaimedBoundary`, and `maxProofsVerified = 1` —
 * and nothing else; it is never described as dregg's chain.
 *
 * ⚑ `relay` IS NEVER CALLED AND IS LOAD-BEARING ANYWAY. Its presence is what
 * makes the program's `maxProofsVerified` 1, which is what `DreggTerminalProof`
 * declares and what dregg's real terminal program is (`RootFriUniform`'s
 * terminal slice verifies its predecessor). Without it every advance below dies
 * at Pickles' `prevs_verified` — the proof's SHAPE, not this gate — and the
 * whole table stops being about `DreggHeadGate`.
 *
 * ⚑ `extraRounds` PERTURBS THE CONSTRAINT SYSTEM so a second producer gets a
 * genuinely different verification key. See the block above: a different NAME
 * gets the same key.
 */
const standIn = (name: string, extraRounds = 0) =>
  ZkProgram({
    name,
    publicInput: Field,
    publicOutput: ClaimedBoundary,
    methods: {
      emit: {
        privateInputs: [Field, ChainClaim],
        async method(bIn: Field, boundary: Field, claim: ChainClaim) {
          let acc = bIn;
          for (let i = 0; i < extraRounds; i++) acc = Poseidon.hash([acc, Field(i)]);
          //  The extra gates must be OBSERVED or the optimiser is free to drop
          //  them and the two keys converge again.
          if (extraRounds > 0) acc.assertNotEquals(Field(0xdead_beefn));
          return { publicOutput: new ClaimedBoundary({ boundary, claim }) };
        },
      },
      relay: {
        privateInputs: [SelfProof<Field, ClaimedBoundary>],
        async method(_bIn: Field, prev: SelfProof<Field, ClaimedBoundary>) {
          prev.verify();
          return { publicOutput: prev.publicOutput };
        },
      },
    },
  });

/** ⚑ ONE PLACE THAT REFUSES A DEGENERATE PRODUCER PAIR. Two producers whose keys
 *  are equal make the vk-pin row and the unpinned control BOTH vacuous, and the
 *  transcript reads identically to a working one. So it is a FAILURE here, in
 *  both the gate phase and the control phase, rather than a printed boolean. */
function assertDistinctKeys(vkA: VerificationKey, vkB: VerificationKey): void {
  if (vkA.hash.toBigInt() === vkB.hash.toBigInt())
    fail(
      'the two stand-in producers compiled to the SAME verification key. Every row below that ' +
        "says 'a DIFFERENT program' would compare two equal fields and pass regardless of what " +
        'the pin does — a green over a false premise, inside the guard whose whole job is proving ' +
        'the anchor binds. See the block above: a program NAME does not enter a Kimchi key.',
    );
}

async function circuitTable(C: ClaimValues, G: bigint) {
  console.log('\n[2] THE GATE, AGAINST A REAL prove()\n');

  //  ⚑ THREE CIRCUITS IN THIS PROCESS, NOT FOUR. §3.20 measured that a node
  //  process which has compiled FOUR step circuits hangs at the first `prove`.
  //  Two stand-ins plus one gate is three; the UNPINNED control is a fourth and
  //  therefore runs in a child process.
  let t = Date.now();
  const A = standIn('dregg-head-standin-A', 0);
  const B = standIn('dregg-head-standin-B', 3);
  const vkA = (await A.compile()).verificationKey;
  const vkB = (await B.compile()).verificationKey;
  assertDistinctKeys(vkA, vkB);
  ok(
    `compiled two stand-in producers with DIFFERENT constraint systems in ${secs(t)} — ` +
      `vk ${hex(vkA.hash.toBigInt())} vs ${hex(vkB.hash.toBigInt())}`,
  );

  const CHAIN_VK_ROOT = Field(0x5eed_beefn);
  //  ⚑ 912 IS THE REAL CHAIN'S LENGTH (`head-anchor-pins` reports 905 uniform
  //  instances + 7 AIR steps) and it is used here so the row reads naturally.
  //  It is the ONLY pin below that is not invented — `CHAIN_VK_ROOT` is a
  //  constant nobody committed to and `terminalVkHash` is stand-in A's. Saying
  //  which is which is the difference between a table and a claim.
  const TOTAL_STEPS = 912;
  const pins: DreggChainPins = {
    label: 'stand-in producer A (leg 22 — NOT dregg\'s chain)',
    terminalVkHash: vkA.hash.toBigInt(),
    chainVkRoot: CHAIN_VK_ROOT.toBigInt(),
    totalSteps: TOTAL_STEPS,
    genesisRoot: G,
  };

  t = Date.now();
  const built = makeDreggHeadGate(pins);
  const Gate = built.DreggHeadGate;
  const analysis = await Gate.analyzeMethods();
  console.log(
    `    advanceHead ${analysis.advanceHead.rows} rows · reportFork ${analysis.reportFork.rows} rows` +
      ` (each verifies one side-loaded proof at FeatureFlags.allMaybe)`,
  );
  await Gate.compile();
  ok(`compiled ${built.variant} in ${secs(t)}`);

  const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
  Mina.setActiveInstance(Local);
  const deployer = Local.testAccounts[0];
  const zkAppKey = PrivateKey.random();
  const app = new Gate(zkAppKey.toPublicKey());

  t = Date.now();
  const dep = await Mina.transaction(deployer, async () => {
    AccountUpdate.fundNewAccount(deployer);
    await app.deploy({
      bootstrap: DreggBootstrap.weakSubjectivityAnchor(Field(G), 'leg 22 stand-in bootstrap'),
    });
  });
  await dep.prove();
  await dep.sign([deployer.key, zkAppKey]).send();
  const canon = canonicalBootstrapState(pins);
  if (app.head.get().toBigInt() !== canon.head.toBigInt() || app.turns.get().toBigInt() !== 0n)
    fail('the deploy did not install the canonical bootstrap state');
  ok(`deployed at the weak-subjectivity anchor in ${secs(t)}, and it reads back as 'genesis'`);

  //  The preimage a caller exhibits. Any two fields whose seal matches is what
  //  an honest caller has; the gate never learns their meaning.
  const fc = Field(0xabcdefn);
  const aod = digestOfLanes([Field(1), Field(2), Field(3)]);
  const honestSeal = terminalSealOf(fc, aod, CHAIN_VK_ROOT, TOTAL_STEPS);
  const cf = claimFieldsOf(C);
  const honestClaim = new ChainClaim(cf);

  const proveStandIn = async (prog: any, boundary: Field, claim: ChainClaim) => {
    const { proof } = await prog.emit(Field(0), boundary, claim);
    return DreggTerminalProof.fromProof(proof);
  };

  type Row = {
    what: string;
    want: 'ACCEPTED' | 'REFUSED';
    run: () => Promise<void>;
    /** ⚑ WHICH ASSERTION. A row that is refused by SOME constraint is not a row
     *  about the constraint it names — the vk pin's row in particular has been
     *  refused before by the proof's SHAPE, which is not this gate at all. */
    msg?: RegExp;
  };
  const send = async (f: () => Promise<void>) => {
    const tx = await Mina.transaction(deployer, f);
    await tx.prove();
    await tx.sign([deployer.key]).send();
  };

  const advance = (p: any, vk: VerificationKey, a = fc, b = aod) => () =>
    send(async () => {
      await app.advanceHead(p, vk, a, b);
    });

  //  ---- the refusals, each aimed at ONE named assertion -------------------
  const refusals: Row[] = [
    {
      what: 'a proof of a DIFFERENT program, under its own real key (the vk pin)',
      want: 'REFUSED',
      run: advance(await proveStandIn(B, honestSeal, honestClaim), vkB),
      msg: /a key this gate does not name/,
    },
    {
      what: 'a mid-chain STEP boundary presented as terminal (the seal exhibition)',
      want: 'REFUSED',
      run: advance(
        await proveStandIn(A, stepBoundary(fc, aod, Field(TOTAL_STEPS)), honestClaim),
        vkA,
      ),
    },
    {
      what: 'a seal under a DIFFERENT key-list root (chainVkRoot)',
      want: 'REFUSED',
      run: advance(
        await proveStandIn(A, terminalSealOf(fc, aod, Field(0xdeadn), TOTAL_STEPS), honestClaim),
        vkA,
      ),
    },
    {
      what: 'a seal at a SHORTER chain (totalSteps — six of nineteen queries)',
      want: 'REFUSED',
      run: advance(
        await proveStandIn(A, terminalSealOf(fc, aod, CHAIN_VK_ROOT, TOTAL_STEPS - 1), honestClaim),
        vkA,
      ),
    },
    {
      what: 'a segment that does not start at the pinned genesis (the extension check)',
      want: 'REFUSED',
      run: advance(
        await proveStandIn(
          A,
          honestSeal,
          new ChainClaim({ ...cf, genesisRoot: Field(4242) }),
        ),
        vkA,
      ),
    },
    {
      what: 'a zero-turn segment',
      want: 'REFUSED',
      run: advance(
        await proveStandIn(A, honestSeal, new ChainClaim({ ...cf, numTurns: Field(0) })),
        vkA,
      ),
    },
    {
      what: 'a fork report on a client that has accepted nothing',
      want: 'REFUSED',
      run: () =>
        send(async () => {
          await app.reportFork(
            DreggTerminalProof.fromProof(
              (await A.emit(Field(0), honestSeal, new ChainClaim({ ...cf, finalRoot: Field(999) })))
                .proof,
            ),
            vkA,
            fc,
            aod,
          );
        }),
    },
  ];

  for (const r of refusals) {
    let accepted = false;
    try {
      await r.run();
      accepted = true;
    } catch (e) {
      const m = String((e as Error)?.message ?? e);
      if (!isConstraintFailure(e))
        fail(`'${r.what}' failed for a reason that is not a constraint failure: ${String(e)}`);
      //  ⚑ `prevs_verified` IS PICKLES, NOT THIS GATE. It says the side-loaded
      //  proof's SHAPE is not the shape the verifier circuit was built for, and
      //  it fires BEFORE any assertion in `DreggHeadGate`. A row "refused" by it
      //  is a row about the harness's producer.
      if (/prevs_verified/.test(m))
        fail(
          `'${r.what}' was refused at Pickles' \`prevs_verified\` — the producer's SHAPE, not this ` +
            'gate. Every row in this table would read REFUSED for that one reason and none of them ' +
            `would be about \`DreggHeadGate\`. Raw:\n${m.slice(0, 600)}`,
        );
      if (r.msg && !r.msg.test(m))
        fail(
          `'${r.what}' was refused, but not by the assertion it names (${r.msg}). A refusal by some ` +
            `other constraint does not make this row attributable. Raw:\n${m.slice(0, 600)}`,
        );
    }
    if (accepted) fail(`'${r.what}' was ACCEPTED and must be refused`);
    console.log(`      REFUSED   ${r.what}`);
  }
  ok(`${refusals.length} refusals, every one a real constraint failure at the assertion it targets`);

  //  ---- the accept, and it must come AFTER the refusals ------------------
  t = Date.now();
  await advance(await proveStandIn(A, honestSeal, honestClaim), vkA)();
  if (app.head.get().toBigInt() !== C.finalRoot || app.turns.get().toBigInt() !== C.numTurns)
    fail('the accepted advance did not move the head to H');
  const wantHistory = historyLink(canon.acceptedHistory, cf);
  if (app.acceptedHistory.get().toBigInt() !== wantHistory.toBigInt())
    fail('the accepted-history link on chain is not the one the exported fold computes');
  ok(`ACCEPTED: head = H, turns = ${C.numTurns}, history link matches the twin (${secs(t)})`);

  //  ---- the fork, now that there is something to conflict with -----------
  const forkClaim = new ChainClaim({ ...cf, finalRoot: Field(0xf0f0n), chainDigest: Field(0xd1d1n) });
  await send(async () => {
    await app.reportFork(await proveStandIn(A, honestSeal, forkClaim), vkA, fc, aod);
  });
  if (app.fork.get().toBigInt() !== forkWitnessOf({ ...cf, finalRoot: Field(0xf0f0n), chainDigest: Field(0xd1d1n) }).toBigInt())
    fail('the fork witness on chain is not the one the exported function computes');
  if (app.head.get().toBigInt() !== C.finalRoot) fail('the fork report MOVED the head — it must not');
  ok('a same-start same-length different-end segment is recorded as a FORK and the head does not move');

  let advancedWhileHalted = false;
  try {
    await advance(
      await proveStandIn(
        A,
        honestSeal,
        new ChainClaim({ ...cf, genesisRoot: Field(C.finalRoot), finalRoot: Field(1234), numTurns: Field(2) }),
      ),
      vkA,
    )();
    advancedWhileHalted = true;
  } catch (e) {
    if (!isConstraintFailure(e)) fail(`the halt refused for a non-constraint reason: ${String(e)}`);
  }
  if (advancedWhileHalted) fail('a HALTED client accepted an advance');
  ok('the halt is ABSORBING — there is no `resolveFork`, and a new anchor is a new deployment');

  return { pins, vkA, vkB, honestSeal, honestClaim: cf, fc, aod };
}

// ===========================================================================
// [3] THE CONTROL — the same object, the pin removed, in its OWN process.
// ===========================================================================

async function control() {
  console.log('\n[3] THE UNPINNED CONTROL — same gate, `vk.hash.assertEquals` removed\n');
  const { claim: C } = realClaim();
  const A = standIn('dregg-head-standin-A', 0);
  const B = standIn('dregg-head-standin-B', 3);
  const vkA = (await A.compile()).verificationKey;
  const vkB = (await B.compile()).verificationKey;
  //  ⚑ THE CONTROL IS ONLY A CONTROL IF B IS FOREIGN. Same refusal as the gate
  //  phase: two equal keys would make "the unpinned gate accepts a foreign
  //  proof" a sentence about a proof that is not foreign.
  assertDistinctKeys(vkA, vkB);

  const CHAIN_VK_ROOT = Field(0x5eed_beefn);
  const TOTAL_STEPS = 912;
  __resetHeadGateFactoryForTest();
  const built = makeDreggHeadGate(
    {
      label: 'stand-in producer A (leg 22 CONTROL)',
      terminalVkHash: vkA.hash.toBigInt(),
      chainVkRoot: CHAIN_VK_ROOT.toBigInt(),
      totalSteps: TOTAL_STEPS,
      genesisRoot: C.genesisRoot,
    },
    { pinVk: false },
  );
  if (built.variant === 'GATE') fail('the control built the GATE — it would prove nothing');
  await built.DreggHeadGate.compile();

  const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
  Mina.setActiveInstance(Local);
  const deployer = Local.testAccounts[0];
  const zkAppKey = PrivateKey.random();
  const app = new built.DreggHeadGate(zkAppKey.toPublicKey());
  const dep = await Mina.transaction(deployer, async () => {
    AccountUpdate.fundNewAccount(deployer);
    await app.deploy({
      bootstrap: DreggBootstrap.weakSubjectivityAnchor(
        Field(C.genesisRoot),
        'leg 22 control bootstrap',
      ),
    });
  });
  await dep.prove();
  await dep.sign([deployer.key, zkAppKey]).send();

  const fc = Field(0xabcdefn);
  const aod = digestOfLanes([Field(1), Field(2), Field(3)]);
  const { proof } = await B.emit(
    Field(0),
    terminalSealOf(fc, aod, CHAIN_VK_ROOT, TOTAL_STEPS),
    new ChainClaim(claimFieldsOf(C)),
  );
  const tx = await Mina.transaction(deployer, async () => {
    await app.advanceHead(DreggTerminalProof.fromProof(proof), vkB, fc, aod);
  });
  await tx.prove();
  await tx.sign([deployer.key]).send();
  if (app.head.get().toBigInt() !== C.finalRoot)
    fail('the UNPINNED control did not accept the foreign proof — then the pinned refusal is not attributable to the pin');
  ok('the UNPINNED gate ACCEPTS producer B\'s proof — so the pinned gate\'s refusal is the PIN');
}

// ===========================================================================
// [4] WHAT ENTERS A VERIFICATION KEY — measured, in its own process.
//
// ⚑ THIS PHASE EXISTS BECAUSE THE ANSWER WAS ASSUMED AND WRONG. Both producers
// above used to differ only in their `name:`, which made the vk-pin row compare
// two equal fields. The three rows here are the discriminating experiment: hold
// everything constant but the name (SAME key), add one gate (DIFFERENT key), add
// a method (DIFFERENT key). Nothing here is read off a doc.
// ===========================================================================

async function vkFacts() {
  console.log('\n[4] WHAT ENTERS A KIMCHI VERIFICATION KEY — three compiles, one variable each\n');

  //  A deliberately tiny program: the point is the DELTA between keys, and a
  //  small circuit measures it as well as a large one for a fraction of the
  //  compile.
  const tiny = (name: string, gates: number, withRelay: boolean) =>
    ZkProgram({
      name,
      publicInput: Field,
      publicOutput: Field,
      methods: {
        emit: {
          privateInputs: [],
          async method(x: Field) {
            let a = x;
            for (let i = 0; i < gates; i++) a = Poseidon.hash([a, Field(i)]);
            if (gates > 0) a.assertNotEquals(Field(0xdead_beefn));
            return { publicOutput: a };
          },
        },
        ...(withRelay
          ? {
              relay: {
                privateInputs: [SelfProof<Field, Field>],
                async method(_x: Field, prev: SelfProof<Field, Field>) {
                  prev.verify();
                  return { publicOutput: prev.publicOutput };
                },
              },
            }
          : {}),
      },
    } as any);

  const t = Date.now();
  const base = (await tiny('vkfacts-BASELINE', 1, false).compile()).verificationKey.hash.toBigInt();
  const renamed = (await tiny('vkfacts-A-DIFFERENT-NAME-ENTIRELY', 1, false).compile())
    .verificationKey.hash.toBigInt();
  const oneMoreGate = (await tiny('vkfacts-BASELINE', 2, false).compile()).verificationKey.hash.toBigInt();
  const oneMoreMethod = (await tiny('vkfacts-BASELINE', 1, true).compile()).verificationKey.hash.toBigInt();

  const rows: [string, bigint, 'SAME' | 'DIFFERENT'][] = [
    ['the program NAME, and nothing else', renamed, 'SAME'],
    ['ONE more Poseidon.hash gate', oneMoreGate, 'DIFFERENT'],
    ['ONE more method (maxProofsVerified 0 → 1)', oneMoreMethod, 'DIFFERENT'],
  ];
  for (const [what, h, want] of rows) {
    const got = h === base ? 'SAME' : 'DIFFERENT';
    if (got !== want)
      fail(
        `changing '${what}' gave a ${got} verification key and this file says ${want}. The ` +
          'description of what enters a Kimchi key in this file is WRONG on this o1js, and every ' +
          'row built on it has to be redone.',
      );
    console.log(`      ${got.padEnd(9)} key   ← ${what}`);
  }
  ok(
    `MEASURED in ${secs(t)}: a Kimchi key commits to the CONSTRAINT SYSTEM and the branch table, ` +
      'and NOT to the program name — so "a proof of a different program" needs different gates',
  );
}

// ===========================================================================

async function main() {
  const t0 = Date.now();
  if (PHASE === 'vkfacts') {
    await vkFacts();
    console.log('\n=== HEAD-ANCHOR VK-FACTS PASS ===\n');
    return;
  }
  if (PHASE === 'control') {
    await control();
    console.log('\n=== HEAD-ANCHOR CONTROL PASS ===\n');
    return;
  }

  console.log('=== HEAD-ANCHOR (leg 22) — the anchor stops being signed ===');
  const { C, G } = differential();

  //  ⚑ THE ROW THAT MATTERS MOST, PRINTED AT EVERY TIER.
  const pins = realPins();
  if (pins === null)
    na(
      "dregg's REAL terminal proof is accepted by `advanceHead`",
      `${PINS_PATH} does not exist. The chain has not been compiled to a key list ` +
        '(terminalVkHash, chainVkRoot, totalSteps) and has not been proved to a terminal proof, so ' +
        'there is nothing to hand the gate. This is a COORDINATOR job — see the BUILD REQUEST in ' +
        'the commit that landed this file. It is not a skip and it is not a failure.',
    );
  else
    ok(
      `a real pin file is present (${pins.label}) — the gate can be built against dregg's own chain`,
    );

  if (!atTier(1)) {
    tierStop(
      'HEAD-ANCHOR',
      checks,
      secs(t0),
      'the LocalBlockchain table (7 refusals, the accept, the fork and the halt) at tier 1, and ' +
        'the UNPINNED control in its own process. Nothing above compiled a circuit.',
    );
    return;
  }

  await circuitTable(C, G);

  //  ⚑ THE CONTROL RUNS IN A CHILD PROCESS, and that is not fastidiousness:
  //  this process has compiled three circuits and §3.20 measured that a fourth
  //  hangs at the first `prove`. The vk-facts phase is a fourth, fifth and sixth
  //  and goes in its own process for the same reason.
  const phase = (name: string, why: string) => {
    console.log(`\n    (spawning ${name} in its own process — ${why})`);
    const r = spawnSync(process.execPath, ['--max-old-space-size=16384', process.argv[1]], {
      env: { ...process.env, HEAD_PHASE: name },
      stdio: 'inherit',
    });
    if (r.status !== 0)
      fail(`the ${name} process exited ${r.status} — the table above is not attributable`);
    checks++;
  };
  phase('control', 'four compiled circuits hang at prove');
  phase('vkfacts', 'it compiles three more, and its answer is what makes the vk pin a pin');

  console.log(`\n=== HEAD-ANCHOR PASS === ${checks} checks, ${secs(t0)}, MINA_TIER=${MINA_TIER}`);
  console.log(
    '    ⚑ WHAT THIS DOES NOT SHOW: that dregg\'s real terminal proof is accepted. The stand-in ' +
      'is not dregg\'s chain; what it makes attributable is the GATE\'s assertions.\n',
  );
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
