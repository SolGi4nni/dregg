// Deploy `DreggAttestedGate` to Mina **DEVNET** and anchor the freshly emitted
// dregg-side root.
//
//   npm run devnet:emit-root && npm run devnet:deploy
//
// Writes `devnet-deployment.json` (public data only: address, VK hashes, tx
// hashes). The private keys stay in `~/.config/dregg-mina/devnet-keys.json`.

import { AccountUpdate, Field, Mina, fetchAccount } from 'o1js';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  ANCHOR_MERKLE_DEPTH,
  DreggAnchorStatement,
  DreggAttestedGate,
  DreggMembershipAttestation,
  anchorLeavesFromSeed,
  proveAnchor,
  signPlaceholderAnchor,
} from '../src/DreggPoseidonAttestation.js';
import type { EmittedRoot } from './devnet-emit-root.js';
import {
  balance,
  connect,
  explorerAcct,
  explorerTx,
  loadKeys,
  mina,
  MINA_ENDPOINT,
  secs,
  until,
} from './devnet-common.js';

const ROOT_JSON = resolve(process.cwd(), 'devnet-root.json');
const DEPLOY_JSON = resolve(process.cwd(), 'devnet-deployment.json');

/** Devnet fees. Generous — a stuck deploy costs more time than a fee does. */
const FEE_DEPLOY = 300_000_000; // 0.3 MINA
const FEE_CALL = 200_000_000; //   0.2 MINA

async function main() {
  console.log('=== deploy DreggAttestedGate to Mina devnet ===');
  connect();
  const { deployerKey, deployer, zkAppKey, zkApp, relayKey, relay } = loadKeys();
  const emitted = JSON.parse(readFileSync(ROOT_JSON, 'utf8')) as EmittedRoot;
  const root = Field(BigInt(emitted.root));

  console.log(`  endpoint : ${MINA_ENDPOINT}`);
  console.log(`  deployer : ${deployer.toBase58()}`);
  console.log(`  zkApp    : ${zkApp.toBase58()}`);
  console.log(`  relay    : ${relay.toBase58()}  (the only key that can re-anchor)`);
  console.log(`  root     : ${emitted.root}`);
  console.log(`             (emitted ${emitted.emittedAt} by ${emitted.emitter})`);

  const bal = await balance(deployer);
  if (bal === null || bal < 2_000_000_000n) {
    console.error(
      `\n  deployer balance is ${bal === null ? 'NO ACCOUNT' : mina(bal)} — need >= 2 MINA.` +
        '\n  Run `npm run devnet:fund`, or fund by hand at' +
        `\n  https://faucet.minaprotocol.com/?address=${deployer.toBase58()} (choose Devnet).`,
    );
    process.exit(1);
  }
  console.log(`  balance  : ${mina(bal)}\n`);

  // --- compile ---------------------------------------------------------------
  // The gate's VK depends on the attestation program's VK (it verifies the proof
  // recursively), so the inner program must be compiled first and BOTH hashes
  // are part of what is deployed.
  let t = Date.now();
  const attVk = (await DreggMembershipAttestation.compile()).verificationKey;
  console.log(`  compiled DreggMembershipAttestation in ${secs(t)}`);
  console.log(`    attestation VK hash: ${attVk.hash.toString()}`);

  // The ANCHOR OBLIGATION. `setDreggRoot` verifies a proof of this, so its VK
  // is part of the gate's VK too.
  t = Date.now();
  const anchorVk = (await DreggAnchorStatement.compile()).verificationKey;
  console.log(`  compiled DreggAnchorStatement (depth ${ANCHOR_MERKLE_DEPTH}) in ${secs(t)}`);
  console.log(`    anchor obligation VK hash: ${anchorVk.hash.toString()}`);

  t = Date.now();
  const gateVk = (await DreggAttestedGate.compile()).verificationKey;
  console.log(`  compiled DreggAttestedGate in ${secs(t)}`);
  console.log(`    zkApp VK hash      : ${gateVk.hash.toString()}\n`);

  const app = new DreggAttestedGate(zkApp);

  // --- deploy ---------------------------------------------------------------
  // Idempotent by design. Devnet block times mean this script can be killed
  // between the two transactions; re-running it must resume rather than try to
  // create an account that already exists (the zkApp key is FIXED in the key
  // file, so a blind retry would just fail).
  console.log('  [1] deploying the zkApp account...');
  let deployHash: string | null = null;
  const existing = (await fetchAccount({ publicKey: zkApp })).account;
  if (existing?.zkapp !== undefined) {
    console.log('      already deployed at this address — skipping the deploy tx.');
  } else {
    t = Date.now();
    const deployTx = await Mina.transaction(
      { sender: deployer, fee: FEE_DEPLOY },
      async () => {
        AccountUpdate.fundNewAccount(deployer);
        await app.deploy({ verificationKey: gateVk, placeholderRelay: relay });
      },
    );
    await deployTx.prove();
    const deployPending = await deployTx.sign([deployerKey, zkAppKey]).send();
    deployHash = deployPending.hash;
    console.log(`      tx ${deployHash}`);
    console.log(`      ${explorerTx(deployHash)}`);

    const deployed = await until(
      async () => (await fetchAccount({ publicKey: zkApp })).account?.zkapp !== undefined,
      'the zkApp account to appear on chain',
    );
    if (!deployed) {
      console.error('      the zkApp account never appeared. Check the explorer link.');
      process.exit(1);
    }
    console.log(`      deployed in ${secs(t)}`);
  }

  // --- anchor the root ------------------------------------------------------
  console.log('\n  [2] anchoring the dregg-emitted root...');
  let anchorHash: string | null = null;
  // The anchored root BEFORE this call. `setDreggRoot` binds the relay's
  // signature to the exact transition `[oldRoot, newRoot]` and pins `oldRoot`
  // as an account precondition, so this read is part of the authorization, not
  // a convenience — a stale read produces a transaction the network refuses.
  const onChainRoot =
    (await fetchAccount({ publicKey: zkApp })).account?.zkapp?.appState?.[0] ?? Field(0);

  // ⚑ WHAT IS ANCHORED IS NOT `emitted.root`. `setDreggRoot` takes a PROOF of
  // `DreggAnchorStatement`, whose statement pins slot 0 of the anchored tree to
  // `Poseidon(R_bb)` for a BabyBear-Poseidon2 MMCS root the prover opened. So
  // the anchored tree is the Rust-emitted leaves with that VOUCH prepended, and
  // the anchored root is the proof's public input — there is no path by which a
  // value the proof does not claim reaches `app_state_0`.
  t = Date.now();
  const anchor = await proveAnchor(
    anchorLeavesFromSeed(BigInt('0x' + emitted.gitCommit.slice(0, 12))),
    0,
    emitted.leaves.map((h) => Field(BigInt(h))),
  );
  console.log(`      proved the anchor obligation in ${secs(t)}`);
  console.log(`      BabyBear vouch : ${anchor.vouch.toString()}`);
  console.log(`      anchored root  : ${anchor.anchoredRoot.toString()}`);
  const anchoredAlready = onChainRoot.toBigInt() === anchor.anchoredRoot.toBigInt();
  if (anchoredAlready) {
    console.log('      the root is already anchored — skipping.');
  } else {
    t = Date.now();
    // ⚑ PLACEHOLDER, not authorization. See `DreggAttestedGate`'s header.
    const auth = signPlaceholderAnchor(relayKey, onChainRoot, anchor.anchoredRoot);
    console.log(
      `      placeholder-signing 0x${onChainRoot.toBigInt().toString(16)} -> ${anchor.anchoredRoot.toString()}`,
    );
    const anchorTx = await Mina.transaction(
      { sender: deployer, fee: FEE_CALL },
      async () => {
        await app.setDreggRoot(anchor.proof, auth);
      },
    );
    await anchorTx.prove();
    const anchorPending = await anchorTx.sign([deployerKey]).send();
    anchorHash = anchorPending.hash;
    console.log(`      tx ${anchorHash}`);
    console.log(`      ${explorerTx(anchorHash)}`);

    const anchored = await until(async () => {
      const r = await fetchAccount({ publicKey: zkApp });
      const s = r.account?.zkapp?.appState?.[0];
      return s !== undefined && s.toBigInt() === anchor.anchoredRoot.toBigInt();
    }, 'the root to be anchored on chain');
    if (!anchored) {
      console.error('      the root never appeared in zkApp state. Check the explorer link.');
      process.exit(1);
    }
    console.log(`      anchored in ${secs(t)}`);
  }

  const record = {
    network: 'mina-devnet',
    endpoint: MINA_ENDPOINT,
    deployedAt: new Date().toISOString(),
    gitCommit: emitted.gitCommit,
    zkAppAddress: zkApp.toBase58(),
    deployerAddress: deployer.toBase58(),
    // ⚑ PLACEHOLDER, recorded as one. The key whose signature `setDreggRoot`
    // still also requires — a stopgap for the FRI verify, NOT the anchor's
    // authorization design. Readable from app_state_2/3.
    placeholderRelayAddress: relay.toBase58(),
    attestationVkHash: attVk.hash.toString(),
    anchorObligationVkHash: anchorVk.hash.toString(),
    zkAppVkHash: gateVk.hash.toString(),
    // The Rust-emitted tree, and the tree that was actually anchored (the
    // former with the BabyBear vouch at slot 0).
    emittedRoot: emitted.root,
    babyBearVouch: anchor.vouch.toString(),
    anchoredRoot: anchor.anchoredRoot.toString(),
    deployTx: deployHash,
    anchorRootTx: anchorHash,
    // `null` where a step was skipped because it had already landed (see the
    // idempotency note above) — an earlier run of this script owns that hash.
    explorer: {
      zkApp: explorerAcct(zkApp.toBase58()),
      deployTx: deployHash === null ? null : explorerTx(deployHash),
      anchorRootTx: anchorHash === null ? null : explorerTx(anchorHash),
    },
  };
  writeFileSync(DEPLOY_JSON, JSON.stringify(record, null, 2) + '\n');

  console.log('\n=== DEPLOYED ===');
  console.log(`  zkApp        : ${zkApp.toBase58()}`);
  console.log(`  zkApp VK hash: ${gateVk.hash.toString()}`);
  console.log(`  anchored root: ${emitted.root}`);
  console.log(`  ${explorerAcct(zkApp.toBase58())}`);
  console.log(`\n  wrote ${DEPLOY_JSON}`);
  console.log('  next: npm run devnet:attest');
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
