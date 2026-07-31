// Deploy the PROOF-GATED anchor `DreggHeadGate` to Mina **DEVNET**.
//
//   npm run devnet:head-deploy               # refuses, and says exactly what is missing
//   npm run devnet:head-deploy -- --broadcast # the outward-facing act
//
// This is `PLACEHOLDER_CUTOVER` phase **P4, first half** (`src/DreggHeadAnchor.ts`
// §7). `DreggAttestedGate.setDreggRoot` moves its root because a NAMED KEY
// signed; `DreggHeadGate.advanceHead` moves its head because dregg's own root
// FRI-STARK verified. The two coexist deliberately until this has run — deleting
// the placeholder relay first would make the OLD anchor world-writable under
// Mina's `editState: proof`, which is strictly worse than a labelled key.
//
// ── WHY THIS SCRIPT REFUSES MORE THAN IT DOES ──────────────────────────────
// Three things must exist before a proof-gated anchor can be deployed AT ALL,
// and each absence is reported as itself rather than collapsed into "not ready":
//
//   1. `dregg-chain-pins.json` — the chain's terminal VK hash, key-list Merkle
//      root, length and genesis anchor, EMITTED by the run that compiles dregg's
//      131-program verification chain. `assertRealPins` refuses a zero or a
//      placeholder. Without it there is no gate to build: the pins are IN THE
//      VERIFICATION KEY, so they decide the deployed ADDRESS.
//   2. A zkApp keypair that has never been used. The live
//      `B62qkiRhX1tKdkYSXRHFASHQHj1tPf5VcLzgUhqkL3kuFViX9ckcSaN` holds
//      `DreggAttestedGate`; deploying a different contract there would either
//      fail or silently replace an account whose record this repo publishes.
//      ⚑ THIS SCRIPT DOES NOT MINT ONE. Key material is the operator's.
//   3. `--broadcast`. Deploying is outward-facing and irreversible.
//
// ── WHAT IT WRITES ─────────────────────────────────────────────────────────
// `devnet-head-deployment.json` — public data only, in the same shape
// `devnet-deployment.json` uses, plus the pins the VK commits to and the
// weak-subjectivity attestation, so a third party can rebuild the gate from the
// record and check that the address follows.

import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { resolve } from 'node:path';
import { AccountUpdate, Field, Mina, PrivateKey, PublicKey, fetchAccount } from 'o1js';
import {
  DreggBootstrap,
  DreggChainPins,
  assertRealPins,
  bootstrapProvenance,
  canonicalBootstrapState,
  makeDreggHeadGate,
} from '../src/DreggHeadAnchor.js';
import {
  balance,
  connect,
  explorerAcct,
  explorerTx,
  KEYS_PATH,
  mina,
  MINA_ENDPOINT,
  secs,
  until,
} from './devnet-common.js';

const PINS_PATH = process.env.HEAD_PINS ?? resolve(process.cwd(), 'dregg-chain-pins.json');
const OUT_PATH = resolve(process.cwd(), 'devnet-head-deployment.json');

/** Fees. Generous: a stuck deploy costs more time than a devnet fee does. */
const FEE_DEPLOY = 300_000_000; // 0.3 MINA

/** The minimum the deployer must hold for a deploy + one advance + slack. */
const NEED_NANO = 3_000_000_000n; // 3 MINA

const BROADCAST = process.argv.includes('--broadcast');

/** Everything that must be true before a byte leaves this machine. */
type Blocker = { id: string; what: string; fix: string };

function loadPins(blockers: Blocker[]): DreggChainPins | null {
  if (!existsSync(PINS_PATH)) {
    blockers.push({
      id: 'PINS',
      what: `${PINS_PATH} does not exist`,
      fix:
        'emit it from the run that compiles dregg\'s verification chain — `npm run head-anchor-pins` ' +
        'against a completed 131-program compile. It carries terminalVkHash, chainVkRoot, ' +
        'totalSteps and genesisRoot, and each is a MEASUREMENT: there is no default and a gate ' +
        'built on one would accept a proof of nothing.',
    });
    return null;
  }
  const j = JSON.parse(readFileSync(PINS_PATH, 'utf8'));
  try {
    return assertRealPins({
      label: String(j.label ?? ''),
      terminalVkHash: BigInt(j.terminalVkHash ?? 0),
      chainVkRoot: BigInt(j.chainVkRoot ?? 0),
      totalSteps: Number(j.totalSteps ?? 0),
      genesisRoot: BigInt(j.genesisRoot ?? 0),
    });
  } catch (e) {
    blockers.push({
      id: 'PINS',
      what: `${PINS_PATH} is not a measurement: ${e instanceof Error ? e.message : String(e)}`,
      fix: 're-emit it from the compile run rather than editing it',
    });
    return null;
  }
}

/**
 * The zkApp keypair for THIS gate.
 *
 * ⚑ READ, NEVER MINTED. `devnet-common.ts:keygen` mints the deployer/zkApp/relay
 * set on first use, and that was the right call for a throwaway set nobody had
 * deployed yet. It is the wrong call HERE: this key decides an address that goes
 * into a published record and that a third party is asked to check, and the
 * account it names must be one nobody has used. Minting it silently inside a
 * deploy script is how a demonstration ends up pointing at an address whose
 * provenance nobody can state. So the field is required, the refusal names the
 * one command that creates it, and the operator runs that command.
 */
function loadHeadKey(blockers: Blocker[]): PrivateKey | null {
  if (!existsSync(KEYS_PATH)) {
    blockers.push({
      id: 'KEYS',
      what: `${KEYS_PATH} does not exist`,
      fix: 'run `npm run devnet:fund`, which mints the throwaway devnet set outside the repo at 0600',
    });
    return null;
  }
  const raw = JSON.parse(readFileSync(KEYS_PATH, 'utf8')) as Record<string, string>;
  if (!raw.headZkAppPrivate) {
    blockers.push({
      id: 'HEAD-KEY',
      what: `${KEYS_PATH} has no \`headZkAppPrivate\` — the proof-gated gate has no address`,
      fix:
        'the existing `zkAppPrivate` is ALREADY DEPLOYED (it holds DreggAttestedGate, recorded in ' +
        'devnet-deployment.json), so it must not be reused. Mint a fresh throwaway pair INTO that ' +
        'file — this script deliberately will not:\n' +
        '        node --input-type=module -e "import {PrivateKey} from \'o1js\';' +
        'import {readFileSync,writeFileSync} from \'node:fs\';' +
        `const p='${KEYS_PATH}';const j=JSON.parse(readFileSync(p,'utf8'));` +
        "if(j.headZkAppPrivate)throw new Error('already present — refusing to overwrite');" +
        "const k=PrivateKey.random();j.headZkAppPrivate=k.toBase58();" +
        "j.headZkAppPublic=k.toPublicKey().toBase58();" +
        "writeFileSync(p,JSON.stringify(j,null,2),{mode:0o600});" +
        'console.log(j.headZkAppPublic)"',
    });
    return null;
  }
  return PrivateKey.fromBase58(raw.headZkAppPrivate);
}

function deployerKeyOf(): { key: PrivateKey; pub: PublicKey } {
  const raw = JSON.parse(readFileSync(KEYS_PATH, 'utf8')) as Record<string, string>;
  const key = PrivateKey.fromBase58(raw.deployerPrivate);
  return { key, pub: key.toPublicKey() };
}

async function main() {
  const t0 = Date.now();
  console.log('=== deploy DreggHeadGate (PROOF-GATED anchor) to Mina devnet ===');
  console.log(`  endpoint : ${MINA_ENDPOINT}`);
  console.log(`  keys     : ${KEYS_PATH}  (0600, OUTSIDE the repo)`);
  console.log(`  pins     : ${PINS_PATH}\n`);

  const blockers: Blocker[] = [];
  const pins = loadPins(blockers);
  const headKey = loadHeadKey(blockers);

  connect(); // asserts devnet before any network call

  //  Balance is checked even when other things block, so one run reports every
  //  blocker rather than one per run.
  let deployer: PublicKey | null = null;
  if (existsSync(KEYS_PATH)) {
    deployer = deployerKeyOf().pub;
    const bal = await balance(deployer);
    console.log(`  deployer : ${deployer.toBase58()}  ${bal === null ? 'NO ACCOUNT' : mina(bal)}`);
    if (bal === null || bal < NEED_NANO)
      blockers.push({
        id: 'FUNDS',
        what: `deployer holds ${bal === null ? 'no account' : mina(bal)}, needs >= ${mina(NEED_NANO)}`,
        fix: `npm run devnet:fund   (or https://faucet.minaprotocol.com/?address=${deployer.toBase58()}, Devnet)`,
      });
  }

  if (headKey) {
    const headPub = headKey.toPublicKey();
    console.log(`  gate     : ${headPub.toBase58()}`);
    const r = await fetchAccount({ publicKey: headPub });
    if (r.account !== undefined)
      blockers.push({
        id: 'ADDRESS-IN-USE',
        what: `${headPub.toBase58()} already exists on devnet`,
        fix:
          'a proof-gated gate must be deployed at a fresh address, because its pins live in its ' +
          'verification key and therefore in its address. Mint a new `headZkAppPrivate`.',
      });
  }

  if (!BROADCAST)
    blockers.push({
      id: 'BROADCAST',
      what: '--broadcast was not given',
      fix:
        'deploying is outward-facing and irreversible, so it is never the default. Re-run with ' +
        '`--broadcast` when the rest of this list is empty.',
    });

  if (blockers.length) {
    console.log(`\n  ${blockers.length} BLOCKER(S) — nothing was broadcast.\n`);
    for (const b of blockers) {
      console.log(`  ✗ ${b.id}: ${b.what}`);
      console.log(`      → ${b.fix}\n`);
    }
    //  ⚑ EXIT 3, not 1. A caller (the demo script) distinguishes "the path is
    //  intact and waiting on a named input" from "something broke".
    console.log('=== HEAD-DEPLOY BLOCKED === the path is intact; the inputs above are not present.\n');
    process.exit(3);
  }

  //  Past here everything above is present and --broadcast was given.
  const p = pins!;
  const zkKey = headKey!;
  const zkApp = zkKey.toPublicKey();
  const { key: depKey } = deployerKeyOf();

  console.log('\n  PINS THE VERIFICATION KEY WILL COMMIT TO');
  console.log(`    label          ${p.label}`);
  console.log(`    terminalVkHash ${p.terminalVkHash}`);
  console.log(`    chainVkRoot    ${p.chainVkRoot}`);
  console.log(`    totalSteps     ${p.totalSteps}`);
  console.log(`    genesisRoot    ${p.genesisRoot}\n`);

  let t = Date.now();
  const built = makeDreggHeadGate(p);
  const Gate = built.DreggHeadGate;
  const { verificationKey } = await Gate.compile();
  console.log(`  compiled ${built.variant} in ${secs(t)}`);
  console.log(`    zkApp VK hash: ${verificationKey.hash.toString()}\n`);

  //  ⚑ THE ONE UNVERIFIABLE ACT, NAMED. The first head has nothing before it.
  const attestation =
    process.env.HEAD_ATTESTATION ??
    `dregg genesis anchor as emitted by the chain compile recorded in ${p.label}`;
  const bootstrap = DreggBootstrap.weakSubjectivityAnchor(Field(p.genesisRoot), attestation);
  console.log('  WEAK-SUBJECTIVITY ANCHOR (checked by nothing, and that is the point)');
  console.log(`    ${attestation}\n`);

  const app = new Gate(zkApp);
  t = Date.now();
  const tx = await Mina.transaction({ sender: deployer!, fee: FEE_DEPLOY }, async () => {
    AccountUpdate.fundNewAccount(deployer!);
    await app.deploy({ bootstrap });
  });
  await tx.prove();
  const sent = await tx.sign([depKey, zkKey]).send();
  const hash = sent.hash;
  console.log(`  deploy submitted in ${secs(t)}: ${hash}`);
  console.log(`  ${explorerTx(hash)}`);

  const landed = await until(
    async () => (await fetchAccount({ publicKey: zkApp })).account !== undefined,
    'the deploy to be included',
  );
  if (!landed) {
    console.error('\n  the account did not appear within the budget. It may still land —');
    console.error(`  check ${explorerTx(hash)} and re-run \`npm run devnet:tx-status -- ${hash}\`.`);
    process.exit(1);
  }

  //  Read the account BACK and say which of three things it is. A deploy that
  //  reports itself is not evidence; the chain reporting it is.
  const acct = (await fetchAccount({ publicKey: zkApp })).account!;
  const s = acct.zkapp!.appState;
  const prov = bootstrapProvenance(
    { head: s[0], prevHead: s[1], turns: s[2], acceptedHistory: s[4], fork: s[5] },
    p,
  );
  const canon = canonicalBootstrapState(p);
  console.log(`\n  read back from chain: ${prov.verdict}`);
  console.log(`    ${prov.why}`);
  if (prov.verdict !== 'genesis') {
    console.error('\n  ✗ the deployed account is NOT at the pinned genesis. Refusing to record it');
    console.error('    as a bootstrap — the head it holds rests on an assertion this script did');
    console.error('    not make.');
    process.exit(1);
  }

  const record = {
    network: 'mina-devnet',
    endpoint: MINA_ENDPOINT,
    contract: 'DreggHeadGate',
    gatedBy: 'PROOF — the terminal proof of dregg\'s root-proof verification chain',
    deployedAt: new Date().toISOString(),
    zkAppAddress: zkApp.toBase58(),
    deployerAddress: deployer!.toBase58(),
    zkAppVkHash: verificationKey.hash.toString(),
    pins: {
      label: p.label,
      terminalVkHash: p.terminalVkHash.toString(),
      chainVkRoot: p.chainVkRoot.toString(),
      totalSteps: p.totalSteps,
      genesisRoot: p.genesisRoot.toString(),
    },
    weakSubjectivityAttestation: attestation,
    bootstrapState: {
      head: canon.head.toString(),
      prevHead: canon.prevHead.toString(),
      turns: '0',
      acceptedHistory: canon.acceptedHistory.toString(),
      fork: '0',
    },
    deployTx: hash,
    explorer: { zkApp: explorerAcct(zkApp.toBase58()), deployTx: explorerTx(hash) },
    supersedesForAnchoring: {
      contract: 'DreggAttestedGate',
      note:
        'the signature-gated anchor is NOT retired by this deploy. PLACEHOLDER_CUTOVER phase P5 ' +
        'retires it, and its trigger is an INCLUDED advanceHead against these pins — see ' +
        'devnet-head-advance.ts.',
    },
  };
  writeFileSync(OUT_PATH, JSON.stringify(record, null, 2) + '\n');
  console.log(`\n  wrote ${OUT_PATH}`);
  console.log(`\n=== HEAD-DEPLOY DONE === ${secs(t0)}`);
  console.log('    ⚑ The head has NOT advanced. This account is at its bootstrap and every head');
  console.log('      it ever holds will have been reached by an accepted proof. Run');
  console.log('      `npm run devnet:head-advance -- --broadcast` to make that true of one.\n');
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
