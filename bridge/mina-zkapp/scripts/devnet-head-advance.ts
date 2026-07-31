// Move the deployed `DreggHeadGate`'s head BECAUSE A PROOF VERIFIED.
//
//   npm run devnet:head-advance                  # refuses, naming what is missing
//   npm run devnet:head-advance -- --broadcast   # the outward-facing act
//
// This is `PLACEHOLDER_CUTOVER` phase **P4, second half**, and it is the single
// observable event that retires the signature-gated anchor: an `advanceHead`
// transaction INCLUDED on Devnet, against pins emitted by a real chain compile,
// consuming dregg's real terminal proof. Not "the gate compiles". Not "the
// stand-in is accepted".
//
// ── THE FOUR ARGUMENTS, AND WHERE EACH COMES FROM ──────────────────────────
// `advanceHead(terminal, vk, friCommit, accOutDigest)`:
//
//   terminal       the proof `root-fri-uniform.ts` writes for the LAST block
//                  position at the LAST query — `proof-<spec>-q<Q>.json`, which
//                  is `proof.toJSON()`.
//   vk             that program's verification key — `key-<spec>.json`. The gate
//                  pins `vk.hash` against `dregg-chain-pins.json:terminalVkHash`,
//                  so a mismatch here is a REFUSAL and not a warning.
//   friCommit      the chain's FRI commitment, and
//   accOutDigest   `digestOfLanes` over the accumulator's closing lanes.
//                  Together with `chainVkRoot` and `totalSteps` these are the
//                  preimage of the TERMINAL SEAL the caller must exhibit. They
//                  are not recoverable from the proof — the seal is a hash — so
//                  the run that produced the chain has to hand them over.
//
// ⚑ THE SEAL PREIMAGE IS EMITTED NOW, AND THAT IS WHAT MAKES AN ADVANCE
// PRESENTABLE. It used to be nowhere: `run-fri-uniform`'s per-instance meta
// records `publicInput`/`publicOutput`/`vkHash` but NOT `friCommit`/
// `accOutDigest`, which lived only inside that script's `context()` and died
// with the process. Two fields that no proof publishes and no artifact recorded
// meant the advance could not be presented AT ALL, whatever the keys said.
// Two emitters write them now, from the artifacts rather than by hand:
//
//   dregg-chain-seal.json                        `npm run head-anchor-pins -- --emit`
//   .fullchain/uniform/terminal-seal-preimage.json   `npm run root-fri-uniform`
//
// This script reads either. What remains a genuine handoff is the PROOF, which
// only the prove run has:
//
//   .fullchain/terminal-handoff.json
//   { "spec": "...", "q": 18,
//     "proofPath": ".fullchain/uniform-claim/proof-<spec>-q18.json",
//     "vkPath":    ".fullchain/uniform-claim/key-<spec>.json" }
//
//   env overrides: HEAD_PROOF HEAD_VK HEAD_FRI_COMMIT HEAD_ACC_OUT_DIGEST
//
// ⚑ AND IF BOTH SOURCES SPEAK THEY MUST AGREE. A handoff from an old prove run
// beside a seal file regenerated after a re-emit is two answers to one question;
// this refuses rather than preferring one.

import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import { Field, Mina, PrivateKey, PublicKey, VerificationKey, fetchAccount } from 'o1js';
import {
  DreggChainPins,
  DreggTerminalProof,
  assertRealPins,
  terminalSealOf,
} from '../src/DreggHeadAnchor.js';
import { makeDreggHeadGate } from '../src/DreggHeadAnchor.js';
import {
  balance,
  connect,
  explorerTx,
  KEYS_PATH,
  mina,
  MINA_ENDPOINT,
  secs,
  until,
} from './devnet-common.js';

const WORK = process.env.HEAD_WORKDIR ?? resolve(process.cwd(), '.fullchain');
const PINS_PATH = process.env.HEAD_PINS ?? resolve(process.cwd(), 'dregg-chain-pins.json');
const DEPLOY_PATH = resolve(process.cwd(), 'devnet-head-deployment.json');
const HANDOFF_PATH = process.env.HEAD_HANDOFF ?? resolve(WORK, 'terminal-handoff.json');
/** The EMITTED seal preimage — `head-anchor-pins.js --emit` writes it. */
const SEAL_PATH = process.env.HEAD_SEAL ?? resolve(process.cwd(), 'dregg-chain-seal.json');
const OUT_PATH = resolve(process.cwd(), 'devnet-head-advance-receipt.json');

const FEE_CALL = 200_000_000; // 0.2 MINA
const BROADCAST = process.argv.includes('--broadcast');

type Blocker = { id: string; what: string; fix: string };

type Handoff = {
  spec?: string;
  q?: number;
  proofPath: string;
  vkPath: string;
  friCommit: string;
  accOutDigest: string;
};

const HANDOFF_SHAPE =
  '{ "spec": "<uniformProgramName of the LAST block position>", "q": <last query index>,\n' +
  '          "proofPath": "<path to proof-<spec>-q<Q>.json — proof.toJSON()>",\n' +
  '          "vkPath":    "<path to key-<spec>.json>" }\n' +
  '        (`friCommit`/`accOutDigest` are optional here — they come from the emitted seal file,\n' +
  '         and if both are present they must AGREE)';

/**
 * The seal preimage, from the artifact that EMITS it.
 *
 * ⚑ THIS IS WHY THE ADVANCE CAN BE PRESENTED AT ALL. `friCommit` and
 * `accOutDigest` are not recoverable from the proof — the boundary it publishes
 * is a hash of them — and until 2026-07-30 no run recorded them, so the two
 * fields had to be typed by a human who had watched a log scroll past. Now
 * `head-anchor-pins.js --emit` writes `dregg-chain-seal.json` from the same
 * artifacts the pins come from, and `root-fri-uniform` writes the same shape at
 * `.fullchain/uniform/terminal-seal-preimage.json`.
 *
 * ⚑ AND IT WEAKENS NOTHING. The preimage is still checked against the proof's
 * own boundary below, out of circuit, and recomputed by the gate in circuit. All
 * that changed is that a DERIVED file supplies it instead of a typed one.
 */
type SealFile = {
  friCommit: string;
  accOutDigest: string;
  /** The chain LENGTH the emitting run measured. Cross-checked against the pins:
   *  the two emitters run at different shapes (46-program vs the 131-program
   *  claim-carrying one) and only the second is the chain the pins name. */
  totalSteps: number | null;
  from: string;
};

function loadSealFile(): SealFile | null {
  for (const p of [SEAL_PATH, resolve(WORK, 'uniform', 'terminal-seal-preimage.json')]) {
    if (!existsSync(p)) continue;
    const j = JSON.parse(readFileSync(p, 'utf8'));
    if (!j.friCommit || !j.accOutDigest) continue;
    return {
      friCommit: String(j.friCommit),
      accOutDigest: String(j.accOutDigest),
      totalSteps: typeof j.totalSteps === 'number' ? j.totalSteps : null,
      from: p,
    };
  }
  return null;
}

function loadHandoff(blockers: Blocker[]): Handoff | null {
  //  Env first: a coordinator holding the values does not need a file.
  const seal = loadSealFile();
  const friCommit = process.env.HEAD_FRI_COMMIT ?? seal?.friCommit;
  const accOutDigest = process.env.HEAD_ACC_OUT_DIGEST ?? seal?.accOutDigest;
  if (seal && !process.env.HEAD_FRI_COMMIT)
    console.log(`  seal preimage from ${seal.from}`);

  if (process.env.HEAD_PROOF && process.env.HEAD_VK && friCommit && accOutDigest)
    return {
      proofPath: process.env.HEAD_PROOF,
      vkPath: process.env.HEAD_VK,
      friCommit,
      accOutDigest,
    };

  if (!existsSync(HANDOFF_PATH)) {
    blockers.push({
      id: 'HANDOFF',
      what: `${HANDOFF_PATH} does not exist — the terminal PROOF is not in hand`,
      fix:
        'the 905-instance prove run must write it. The seal preimage no longer has to be in\n' +
        '        it: `npm run head-anchor-pins -- --emit` writes `dregg-chain-seal.json` and\n' +
        '        `npm run root-fri-uniform` writes `.fullchain/uniform/terminal-seal-preimage.json`,\n' +
        '        and this script reads either. What only the prove run has is the PROOF. Shape:\n\n        ' +
        HANDOFF_SHAPE +
        '\n\n        Or set HEAD_PROOF and HEAD_VK (and HEAD_FRI_COMMIT / HEAD_ACC_OUT_DIGEST to\n' +
        '        override the emitted seal).',
    });
    return null;
  }
  const j = JSON.parse(readFileSync(HANDOFF_PATH, 'utf8')) as Partial<Handoff>;
  const merged: Partial<Handoff> = {
    ...j,
    friCommit: j.friCommit ?? friCommit,
    accOutDigest: j.accOutDigest ?? accOutDigest,
  };
  const missing = (['proofPath', 'vkPath', 'friCommit', 'accOutDigest'] as const).filter(
    (k) => !merged[k],
  );
  if (missing.length) {
    blockers.push({
      id: 'HANDOFF',
      what:
        `${HANDOFF_PATH} is missing ${missing.join(', ')}` +
        (seal ? '' : ', and no emitted seal file was found either'),
      fix:
        '`proofPath`/`vkPath` come from the prove run and have no other source. `friCommit`/\n' +
        '        `accOutDigest` are emitted — run `npm run head-anchor-pins -- --emit`.\n        ' +
        HANDOFF_SHAPE,
    });
    return null;
  }
  //  ⚑ IF BOTH SOURCES SPEAK, THEY MUST AGREE. A handoff written by an old prove
  //  run beside a seal file regenerated after a re-emit is two answers to one
  //  question, and silently preferring either is how a wrong preimage reaches a
  //  fee-paying broadcast.
  if (seal && j.friCommit && j.friCommit !== seal.friCommit) {
    blockers.push({
      id: 'SEAL-DISAGREE',
      what: `${HANDOFF_PATH} and ${seal.from} give DIFFERENT friCommit values`,
      fix:
        `handoff ${j.friCommit} vs emitted ${seal.friCommit}. One of the two is from a stale run.\n` +
        '        Re-emit both rather than choosing: `npm run head-anchor-pins -- --emit`.',
    });
    return null;
  }
  if (seal && j.accOutDigest && j.accOutDigest !== seal.accOutDigest) {
    blockers.push({
      id: 'SEAL-DISAGREE',
      what: `${HANDOFF_PATH} and ${seal.from} give DIFFERENT accOutDigest values`,
      fix: `handoff ${j.accOutDigest} vs emitted ${seal.accOutDigest}. One of the two is stale.`,
    });
    return null;
  }
  return merged as Handoff;
}

function loadPins(blockers: Blocker[]): DreggChainPins | null {
  if (!existsSync(PINS_PATH)) {
    blockers.push({
      id: 'PINS',
      what: `${PINS_PATH} does not exist`,
      fix: 'emit it with `npm run head-anchor-pins -- --emit` against a completed 131-program compile',
    });
    return null;
  }
  const j = JSON.parse(readFileSync(PINS_PATH, 'utf8'));
  return assertRealPins({
    label: j.label,
    terminalVkHash: BigInt(j.terminalVkHash),
    chainVkRoot: BigInt(j.chainVkRoot),
    totalSteps: Number(j.totalSteps),
    genesisRoot: BigInt(j.genesisRoot),
  });
}

async function main() {
  const t0 = Date.now();
  console.log('=== advanceHead — move DreggHeadGate BECAUSE A PROOF VERIFIED ===');
  console.log(`  endpoint : ${MINA_ENDPOINT}`);
  console.log(`  pins     : ${PINS_PATH}`);
  console.log(`  handoff  : ${HANDOFF_PATH}\n`);

  const blockers: Blocker[] = [];
  const pins = loadPins(blockers);
  const handoff = loadHandoff(blockers);

  //  ⚑ THE SEAL FILE AND THE PINS MUST NAME THE SAME CHAIN. Two emitters write
  //  this shape and they run at DIFFERENT chain shapes — `root-fri-uniform` at
  //  the 46-program §3.29 walk (827 steps) and `head-anchor-pins` at the
  //  131-program claim-carrying one (912). Only the second is the chain the pins
  //  name. `friCommit`/`accOutDigest` happen to agree between them today, so the
  //  MISMATCH IS INVISIBLE in those two fields and would surface as an opaque
  //  seal comparison failure after the compile. Named here instead.
  {
    const seal = loadSealFile();
    if (seal && pins && seal.totalSteps !== null && seal.totalSteps !== pins.totalSteps)
      blockers.push({
        id: 'SEAL-SHAPE',
        what:
          `${seal.from} was emitted for a ${seal.totalSteps}-step chain and the pins name ` +
          `${pins.totalSteps} steps — two different chain shapes`,
        fix:
          'the anchor\'s chain is the claim-carrying one. Emit the seal from the SAME run the\n' +
          '        pins come from: `npm run head-anchor-pins -- --emit`, which writes\n' +
          `        dregg-chain-seal.json. Do not hand-copy fields between the two files.`,
      });
  }

  if (!existsSync(DEPLOY_PATH))
    blockers.push({
      id: 'DEPLOYMENT',
      what: `${DEPLOY_PATH} does not exist — there is no proof-gated gate to advance`,
      fix: 'npm run devnet:head-deploy -- --broadcast',
    });

  if (!existsSync(KEYS_PATH))
    blockers.push({
      id: 'KEYS',
      what: `${KEYS_PATH} does not exist`,
      fix: 'npm run devnet:fund',
    });

  //  Artifacts, checked before the network so one run reports every blocker.
  if (handoff) {
    for (const [k, p] of [
      ['proofPath', handoff.proofPath],
      ['vkPath', handoff.vkPath],
    ] as const)
      if (!existsSync(resolve(p)))
        blockers.push({
          id: 'ARTIFACT',
          what: `${k} points at ${p}, which does not exist`,
          fix: 'the 905-instance prove run writes these; a handoff naming an absent file is a stale handoff',
        });
  }

  if (!BROADCAST)
    blockers.push({
      id: 'BROADCAST',
      what: '--broadcast was not given',
      fix: 'submitting a transaction is outward-facing and irreversible, so it is never the default',
    });

  connect();

  let deployer: PublicKey | null = null;
  let depKey: PrivateKey | null = null;
  if (existsSync(KEYS_PATH)) {
    const raw = JSON.parse(readFileSync(KEYS_PATH, 'utf8')) as Record<string, string>;
    depKey = PrivateKey.fromBase58(raw.deployerPrivate);
    deployer = depKey.toPublicKey();
    const bal = await balance(deployer);
    console.log(`  deployer : ${deployer.toBase58()}  ${bal === null ? 'NO ACCOUNT' : mina(bal)}`);
    if (bal === null || bal < 1_000_000_000n)
      blockers.push({
        id: 'FUNDS',
        what: `deployer holds ${bal === null ? 'no account' : mina(bal)}, needs >= 1 MINA`,
        fix: 'npm run devnet:fund',
      });
  }

  if (blockers.length) {
    console.log(`\n  ${blockers.length} BLOCKER(S) — nothing was broadcast.\n`);
    for (const b of blockers) {
      console.log(`  ✗ ${b.id}: ${b.what}`);
      console.log(`      → ${b.fix}\n`);
    }
    console.log('=== HEAD-ADVANCE BLOCKED === the path is intact; the inputs above are not present.\n');
    process.exit(3);
  }

  const p = pins!;
  const h = handoff!;
  const deployment = JSON.parse(readFileSync(DEPLOY_PATH, 'utf8'));
  const zkApp = PublicKey.fromBase58(deployment.zkAppAddress);
  console.log(`  gate     : ${zkApp.toBase58()}\n`);

  //  ---- the gate, rebuilt from the SAME pins the deploy recorded ----------
  //  ⚑ Rebuilt, not assumed: if the pin file has moved since the deploy, the VK
  //  moves with it and the address stops corresponding. Comparing here turns a
  //  silent mismatch into a refusal before a fee is spent.
  let t = Date.now();
  const built = makeDreggHeadGate(p);
  const Gate = built.DreggHeadGate;
  const { verificationKey } = await Gate.compile();
  console.log(`  compiled ${built.variant} in ${secs(t)}`);
  if (verificationKey.hash.toString() !== String(deployment.zkAppVkHash)) {
    console.error('\n  ✗ the gate compiled from the current pins has a DIFFERENT verification key');
    console.error(`      deployed : ${deployment.zkAppVkHash}`);
    console.error(`      current  : ${verificationKey.hash.toString()}`);
    console.error('    The pins moved since the deploy. The deployed address does not correspond to');
    console.error('    these sources, so this advance would be built against a gate that is not the');
    console.error('    one on chain. Re-deploy at the new pins rather than advancing.');
    process.exit(1);
  }
  console.log('    VK matches the deployed record\n');

  //  ---- the proof and its key --------------------------------------------
  const vkJson = JSON.parse(readFileSync(resolve(h.vkPath), 'utf8'));
  const vk = new VerificationKey({
    data: vkJson.data ?? vkJson.verificationKey?.data,
    hash: Field(BigInt(vkJson.hash ?? vkJson.verificationKey?.hash)),
  });
  if (vk.hash.toBigInt() !== p.terminalVkHash) {
    console.error('\n  ✗ the supplied verification key is not the one the pins name.');
    console.error(`      pinned   : ${p.terminalVkHash}`);
    console.error(`      supplied : ${vk.hash.toString()}`);
    console.error('    The gate would refuse this in circuit; refusing here saves the fee.');
    process.exit(1);
  }

  const terminal = await DreggTerminalProof.fromJSON(
    JSON.parse(readFileSync(resolve(h.proofPath), 'utf8')),
  );
  const friCommit = Field(BigInt(h.friCommit));
  const accOutDigest = Field(BigInt(h.accOutDigest));

  //  ---- the seal, exhibited and CHECKED OUT OF CIRCUIT FIRST -------------
  //  The gate recomputes this; doing it here too means a mismatch is a printed
  //  comparison rather than an opaque constraint failure inside a Pickles prove.
  const expected = terminalSealOf(friCommit, accOutDigest, Field(p.chainVkRoot), p.totalSteps);
  const actual = (terminal.publicOutput as any).boundary as Field;
  console.log('  TERMINAL SEAL');
  console.log(`    exhibited preimage → ${expected.toString()}`);
  console.log(`    proof's boundary   → ${actual.toString()}`);
  if (expected.toBigInt() !== actual.toBigInt()) {
    console.error('\n  ✗ the exhibited preimage does not reproduce the proof\'s boundary.');
    console.error('    Either friCommit/accOutDigest are from a different run, or this proof is not');
    console.error('    the TERMINAL one (a mid-chain step boundary is 3 fields, a seal is 4).');
    process.exit(1);
  }
  console.log('    they agree — this is the chain\'s terminal seal at the pinned length\n');

  const claim = (terminal.publicOutput as any).claim;
  console.log('  THE CLAIM THIS ADVANCE COMMITS TO');
  console.log(`    G ${claim.genesisRoot.toString()}`);
  console.log(`    H ${claim.finalRoot.toString()}`);
  console.log(`    N ${claim.numTurns.toString()}`);
  console.log(`    D ${claim.chainDigest.toString()}\n`);

  //  ---- the transaction ---------------------------------------------------
  const app = new Gate(zkApp);
  await fetchAccount({ publicKey: zkApp });
  const headBefore = app.head.get().toString();
  const turnsBefore = app.turns.get().toString();
  console.log(`  head before : ${headBefore}   turns ${turnsBefore}`);

  t = Date.now();
  const tx = await Mina.transaction({ sender: deployer!, fee: FEE_CALL }, async () => {
    await app.advanceHead(terminal, vk, friCommit, accOutDigest);
  });
  await tx.prove();
  const sent = await tx.sign([depKey!]).send();
  console.log(`  advanceHead submitted in ${secs(t)}: ${sent.hash}`);
  console.log(`  ${explorerTx(sent.hash)}`);

  const moved = await until(async () => {
    await fetchAccount({ publicKey: zkApp });
    return app.head.get().toString() !== headBefore;
  }, 'the head to move on chain');

  if (!moved) {
    console.error('\n  ✗ the head did not move within the budget.');
    console.error('    ⚑ A zkApp transaction whose precondition failed is INCLUDED AND FAILED — it');
    console.error('      spends the fee and bumps the nonce. "The state did not change" is only');
    console.error('      circumstantial. Get the daemon to say it:');
    console.error(`        npm run devnet:tx-status -- ${sent.hash}`);
    process.exit(1);
  }

  await fetchAccount({ publicKey: zkApp });
  const headAfter = app.head.get().toString();
  const turnsAfter = app.turns.get().toString();
  console.log(`\n  head after  : ${headAfter}   turns ${turnsAfter}`);

  const receipt = {
    network: 'mina-devnet',
    endpoint: MINA_ENDPOINT,
    contract: 'DreggHeadGate',
    zkAppAddress: zkApp.toBase58(),
    advancedAt: new Date().toISOString(),
    tx: sent.hash,
    explorer: explorerTx(sent.hash),
    before: { head: headBefore, turns: turnsBefore },
    after: { head: headAfter, turns: turnsAfter },
    claim: {
      genesisRoot: claim.genesisRoot.toString(),
      finalRoot: claim.finalRoot.toString(),
      numTurns: claim.numTurns.toString(),
      chainDigest: claim.chainDigest.toString(),
    },
    terminalVkHash: vk.hash.toString(),
    sealPreimage: { friCommit: h.friCommit, accOutDigest: h.accOutDigest },
    whatThisEstablishes:
      "dregg's state went from G to H in N turns with ordered-history commitment D, G was the " +
      'head this client already held, and a batch-STARK over the root\'s seven AIRs verified for ' +
      'exactly that claim, under the key list this gate\'s verification key names.',
    whatItDoesNot:
      'that the committed function is low degree (the FRI/STARK soundness floor is undischarged); ' +
      'that H is the head dregg FINALIZED (a segment proof establishes executability, not ' +
      'canonicity — no committee signature or blocklace certificate rides in it).',
  };
  writeFileSync(OUT_PATH, JSON.stringify(receipt, null, 2) + '\n');
  console.log(`  wrote ${OUT_PATH}`);
  console.log(`\n=== HEAD-ADVANCE DONE === ${secs(t0)}`);
  console.log('    ⚑ This is PLACEHOLDER_CUTOVER\'s P4 trigger. P5 — deleting placeholderRelay,');
  console.log('      DreggAttestedGate and setDreggRoot — is now unblocked.\n');
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
