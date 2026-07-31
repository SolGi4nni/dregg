// HEAD-GATE REHEARSAL — the deploy path for `DreggHeadGate`, end to end, with
// nothing that depends on dregg's rotating verification keys.
//
//   npm run head-gate-rehearsal
//
// ── WHY THIS EXISTS BESIDE `head-anchor` ───────────────────────────────────
// `head-anchor.ts` at `MINA_TIER=1` is the assertion table for the gate. This is
// the DEPLOY REHEARSAL: does an operator who has the pins get a deployed account
// whose head moves because a proof verified. Different question, and it is the
// one the runbook's step 4 stakes a broadcast on.
//
// ⚑ AND IT WAS WRITTEN BECAUSE THE TABLE'S ACCEPT ROW IS RED. Measured
// 2026-07-30 22:5x on this tree, `MINA_TIER=1 npm run head-anchor`:
//
//     ✓ compiled two stand-in producers in 19.7s (vk hashes differ: false)
//     ✓ 7 refusals, every one a real constraint failure ...
//     Error: Constraint unsatisfied (unreduced) ... prevs_verified
//
// Two things in that transcript, and neither is the gate:
//
//   * `vk hashes differ: FALSE`. The two stand-ins are structurally identical
//     programs with different NAMES, and an o1js verification key does not
//     depend on the name. So the row aimed at the vk pin cannot have been
//     refused BY the vk pin — the pin compares two equal fields and passes.
//   * the HONEST ACCEPT then fails at `prevs_verified`, which is Pickles saying
//     the side-loaded proof's SHAPE is not the shape the verifier circuit was
//     built for.
//
// Section [0] below MEASURES which shape, rather than asserting one. The
// hypothesis under test is `maxProofsVerified`: `DreggTerminalProof` declares
// `1` (correct for the real object — `RootFriUniform`'s terminal program
// verifies its predecessor), while a stand-in with no proof input is `0`.
//
// ── SO THE PRODUCERS HERE ARE THE RIGHT SHAPE, AND DIFFER ──────────────────
// Both stand-ins have a `step` method that verifies a `SelfProof`, which makes
// their `maxProofsVerified` 1. And producer B carries EXTRA CONSTRAINTS, so its
// verification key genuinely differs from A's — which is what makes the vk-pin
// refusal attributable instead of a green over a false premise.
//
// ⚑ WHAT A STAND-IN IS NOT. It is not dregg's chain and is never described as
// one. What it makes attributable is the DEPLOY PATH and the gate's assertions.

import {
  Field,
  Mina,
  Poseidon,
  PrivateKey,
  SelfProof,
  VerificationKey,
  ZkProgram,
} from 'o1js';
import { ChainClaim, ClaimedBoundary } from '../src/RootClaim.js';
import {
  DreggBootstrap,
  DreggChainPins,
  DreggTerminalProof,
  bootstrapProvenance,
  claimFieldsOf,
  makeDreggHeadGate,
  terminalSealOf,
} from '../src/DreggHeadAnchor.js';

const t0 = Date.now();
const secs = (t: number) => `${((Date.now() - t) / 1000).toFixed(1)}s`;
let checks = 0;
const ok = (m: string) => {
  checks++;
  console.log(`  ✓ ${m}`);
};
const fail = (m: string): never => {
  console.error(`\n✗ ${m}`);
  process.exit(1);
};

/** §3.28's rule: a `TypeError` inside a bare catch is indistinguishable from a
 *  refusal, so every caught error must be shown to be a constraint failure. */
function isConstraintFailure(e: unknown): boolean {
  const m = String((e as Error)?.message ?? e);
  if (/TypeError|is not a function|undefined is not|Cannot read|ENOENT/.test(m)) return false;
  return /[Cc]onstraint unsatisfied|Constraint failed|assert|not satisfied|DreggHeadGate/i.test(m);
}

/**
 * A producer of the RIGHT SHAPE: `publicOutput: ClaimedBoundary`, and a method
 * that verifies one proof, so `maxProofsVerified === 1` — the same as the real
 * terminal program and the same as `DreggTerminalProof` declares.
 *
 * `extraRounds > 0` perturbs the constraint system so the verification key
 * genuinely differs. It is not decoration: without it "a proof of a DIFFERENT
 * program" is a proof under the SAME key and the vk pin is untested.
 */
const producer = (name: string, extraRounds: number) =>
  ZkProgram({
    name,
    publicInput: Field,
    publicOutput: ClaimedBoundary,
    methods: {
      emit: {
        privateInputs: [Field, ChainClaim],
        async method(seed: Field, boundary: Field, claim: ChainClaim) {
          let acc = seed;
          for (let i = 0; i < extraRounds; i++) acc = Poseidon.hash([acc, Field(i)]);
          //  The extra work must be OBSERVED or the optimiser may drop it.
          acc.assertNotEquals(Field(0xdead_beefn));
          return { publicOutput: new ClaimedBoundary({ boundary, claim }) };
        },
      },
      //  The method that makes maxProofsVerified = 1. Never called: its presence
      //  is what fixes the SHAPE, which is the whole point of this file.
      relay: {
        privateInputs: [SelfProof<Field, ClaimedBoundary>],
        async method(_seed: Field, prev: SelfProof<Field, ClaimedBoundary>) {
          prev.verify();
          return { publicOutput: prev.publicOutput };
        },
      },
    },
  });

async function main() {
  console.log('=== HEAD-GATE REHEARSAL — the deploy path, VK-independent ===\n');
  console.log('[0] THE SHAPE OF A SIDE-LOADED PROOF — measured, not assumed\n');

  console.log(`    DreggTerminalProof.maxProofsVerified = ${DreggTerminalProof.maxProofsVerified}`);

  //  ---- the FALSE PREMISE, reproduced ------------------------------------
  //  Two structurally identical programs, different names. If their keys match,
  //  every "different program" row built on that pair is untested.
  let t = Date.now();
  const twinA = producer('rehearsal-twin-A', 0);
  const twinB = producer('rehearsal-twin-B', 0);
  const tvkA = (await twinA.compile()).verificationKey;
  const tvkB = (await twinB.compile()).verificationKey;
  const namesAlone = tvkA.hash.toBigInt() === tvkB.hash.toBigInt();
  console.log(
    `    two programs differing ONLY in name compile to ${namesAlone ? 'THE SAME' : 'different'} vk hash` +
      ` (${secs(t)})`,
  );
  if (!namesAlone)
    fail(
      'two name-only-different programs got different keys — the premise this file was written ' +
        'around does not hold on this o1js, and the diagnosis above must be redone',
    );
  ok(
    'MEASURED: an o1js verification key does not depend on the program NAME, so a "different ' +
      'program" row needs a different CONSTRAINT SYSTEM, not a different name',
  );

  //  ---- the producers this rehearsal actually uses ------------------------
  //  Fresh classes, because the twins above are already compiled in this
  //  process and o1js identifies a program by its class.
  t = Date.now();
  const A = producer('dregg-head-rehearsal-A', 0);
  const B = producer('dregg-head-rehearsal-B', 3);
  const vkA = (await A.compile()).verificationKey;
  const vkB = (await B.compile()).verificationKey;
  if (vkA.hash.toBigInt() === vkB.hash.toBigInt())
    fail('producers A and B share a verification key — the vk-pin row below would test nothing');
  ok(`two producers with DIFFERENT constraint systems and therefore different keys (${secs(t)})`);

  // =======================================================================
  console.log('\n[1] THE GATE — deployed at a weak-subjectivity anchor\n');

  const GENESIS = 0x7393_bc8b_0218_6f4bn;
  const CHAIN_VK_ROOT = Field(0x5eed_beefn);
  const TOTAL_STEPS = 912; // the real chain's length (905 uniform + 7 AIR)
  const pins: DreggChainPins = {
    label: 'rehearsal producer A — NOT dregg\'s chain, and never reported as one',
    terminalVkHash: vkA.hash.toBigInt(),
    chainVkRoot: CHAIN_VK_ROOT.toBigInt(),
    totalSteps: TOTAL_STEPS,
    genesisRoot: GENESIS,
  };

  t = Date.now();
  const built = makeDreggHeadGate(pins);
  const Gate = built.DreggHeadGate;
  await Gate.compile();
  ok(`compiled ${built.variant} in ${secs(t)}`);

  const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
  Mina.setActiveInstance(Local);
  const deployer = Local.testAccounts[0];
  const zkAppKey = PrivateKey.random();
  const app = new Gate(zkAppKey.toPublicKey());

  t = Date.now();
  const bootstrap = DreggBootstrap.weakSubjectivityAnchor(
    Field(GENESIS),
    'rehearsal anchor — the operator asserting dregg genesis out of band, which is what this is',
  );
  const dep = await Mina.transaction(deployer, async () => {
    const { AccountUpdate } = await import('o1js');
    AccountUpdate.fundNewAccount(deployer);
    await app.deploy({ bootstrap });
  });
  await dep.prove();
  await dep.sign([deployer.key, zkAppKey]).send();
  const prov = bootstrapProvenance(
    {
      head: app.head.get(),
      prevHead: app.prevHead.get(),
      turns: app.turns.get(),
      acceptedHistory: app.acceptedHistory.get(),
      fork: app.fork.get(),
    },
    pins,
  );
  if (prov.verdict !== 'genesis')
    fail(`the deployed account reads back as '${prov.verdict}', not 'genesis'`);
  ok(`deployed and read back as 'genesis' in ${secs(t)}`);

  // =======================================================================
  console.log('\n[2] THE ACCEPT — the row `head-anchor` at MINA_TIER=1 cannot get past\n');

  const fc = Field(0xabc_defn);
  const aod = Field(0x1234_5678n);
  const seal = terminalSealOf(fc, aod, CHAIN_VK_ROOT, TOTAL_STEPS);
  const claim = new ChainClaim(
    claimFieldsOf({
      genesisRoot: GENESIS,
      finalRoot: 0xbf44_62ee_d341_1e40n,
      numTurns: 3n,
      chainDigest: 0xc5e2_9be1_a98a_f1ddn,
    }),
  );

  const prove = async (prog: any, boundary: Field, c: ChainClaim) => {
    const { proof } = await prog.emit(Field(0), boundary, c);
    return DreggTerminalProof.fromProof(proof);
  };

  const advance = async (p: DreggTerminalProof, vk: VerificationKey) => {
    const tx = await Mina.transaction(deployer, async () => {
      await app.advanceHead(p, vk, fc, aod);
    });
    await tx.prove();
    await tx.sign([deployer.key]).send();
  };

  t = Date.now();
  const honest = await prove(A, seal, claim);
  console.log(`    produced a correctly-shaped terminal proof in ${secs(t)}`);
  console.log(
    `    its maxProofsVerified = ${(honest as any).maxProofsVerified ?? '(not surfaced)'}` +
      `, the class declares ${DreggTerminalProof.maxProofsVerified}`,
  );

  t = Date.now();
  try {
    await advance(honest, vkA);
  } catch (e) {
    const m = String((e as Error)?.message ?? e);
    if (/prevs_verified/.test(m))
      fail(
        'the HONEST advance still fails at `prevs_verified` even with a maxProofsVerified=1 ' +
          'producer. The shape hypothesis in this file\'s header is REFUTED and the cause is ' +
          `something else. Raw:\n${m.slice(0, 900)}`,
      );
    fail(`the honest advance was refused: ${m.slice(0, 900)}`);
  }
  if (app.head.get().toBigInt() !== 0xbf44_62ee_d341_1e40n)
    fail('the advance was accepted but the head did not move to H');
  if (app.turns.get().toBigInt() !== 3n) fail('the advance did not set turns to N');
  ok(`ACCEPTED: the head moved to H and turns = 3, in ${secs(t)}`);
  ok(
    'MEASURED: a stand-in whose `maxProofsVerified` matches `DreggTerminalProof` IS accepted — ' +
      'so `head-anchor`\'s accept row fails on its PRODUCER\'s shape, not on the gate',
  );

  // =======================================================================
  console.log('\n[3] THE REFUSALS THIS PATH DEPENDS ON — each against a real prove()\n');

  const refusals: { what: string; run: () => Promise<void> }[] = [
    {
      what: 'a proof of a DIFFERENT program, under its own real key (the vk pin)',
      run: async () => advance(await prove(B, seal, claim), vkB),
    },
    {
      what: 'a seal under a DIFFERENT key-list root (chainVkRoot)',
      run: async () =>
        advance(await prove(A, terminalSealOf(fc, aod, Field(0xdeadn), TOTAL_STEPS), claim), vkA),
    },
    {
      what: 'a seal at a SHORTER chain (totalSteps)',
      run: async () =>
        advance(
          await prove(A, terminalSealOf(fc, aod, CHAIN_VK_ROOT, TOTAL_STEPS - 1), claim),
          vkA,
        ),
    },
    {
      what: 'a segment that does not start at this client\'s head (the extension check)',
      run: async () =>
        advance(
          await prove(
            A,
            seal,
            new ChainClaim(
              claimFieldsOf({
                genesisRoot: 4242n,
                finalRoot: 999n,
                numTurns: 1n,
                chainDigest: 7n,
              }),
            ),
          ),
          vkA,
        ),
    },
  ];

  for (const r of refusals) {
    let accepted = false;
    try {
      await r.run();
      accepted = true;
    } catch (e) {
      if (!isConstraintFailure(e))
        fail(`'${r.what}' failed for a reason that is not a constraint failure: ${String(e)}`);
    }
    if (accepted) fail(`'${r.what}' was ACCEPTED and must be refused`);
    console.log(`      REFUSED   ${r.what}`);
  }
  ok(`${refusals.length} refusals, every one a real constraint failure`);

  console.log(`\n=== HEAD-GATE REHEARSAL PASS === ${checks} checks, ${secs(t0)}`);
  console.log('    ⚑ WHAT THIS SHOWS: an operator holding real pins gets a deployed account whose');
  console.log('      head moves when a correctly-shaped terminal proof verifies under the pinned');
  console.log('      key at the pinned chain length, and does not otherwise.');
  console.log('    ⚑ WHAT IT DOES NOT: that dregg\'s REAL terminal proof is accepted. The producer');
  console.log('      here is a stand-in. That row needs the 131-program compile and the');
  console.log('      905-instance prove, and nothing here stands in for them.\n');
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
