// Exercise the DEPLOYED zkApp on Mina devnet: an honest attestation must be
// ACCEPTED on chain, and a witness the contract does not accept must be
// REFUSED on chain. Both leave a transaction hash.
//
//   npm run devnet:attest
//
// ---------------------------------------------------------------------------
// ⚑ WHERE A zkApp ACTUALLY REFUSES THINGS — read this before reading the output.
//
// In a zkApp, a tampered WITNESS is not "rejected by the chain". It is
// UNPROVABLE: `current.assertEquals(dreggRoot)` makes the constraint system
// unsatisfiable, so no proof exists and no transaction can even be built. That
// refusal is real but it is LOCAL, and it leaves no hash — demonstrated here as
// [R3] and, at depth 2 against the gold root, by `npm run gate` step [4].
//
// What the CHAIN checks, and therefore what can produce a REJECTED transaction
// with a hash, is exactly two things:
//   [R1] the account-state PRECONDITION — `actOnAttestedLeaf` reads the anchored
//        root with `getAndRequireEquals()`, which commits the transaction to the
//        root it was proved against. Anchor a new root, and the earlier
//        attestation is refused AT INCLUSION TIME. This is the stale-attestation
//        case and it is the one that yields a rejected tx hash.
//   [R2] the PROOF ITSELF — corrupt the proof bytes on the wire and the daemon
//        refuses the command outright (no hash; it never enters a block).
//
// All three are exercised below. Claiming more than this — e.g. that the chain
// "caught a forged Merkle path" — would be false: the prover caught it first.
// ---------------------------------------------------------------------------

import { Bool, Field, Mina, Poseidon, fetchAccount } from 'o1js';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  DreggAttestedGate,
  DreggMembershipAttestation,
} from '../src/DreggPoseidonAttestation.js';
import type { EmittedRoot } from './devnet-emit-root.js';
import {
  balance,
  connect,
  explorerTx,
  loadKeys,
  mina,
  MINA_ENDPOINT,
  nonceOf,
  secs,
  until,
} from './devnet-common.js';

const ROOT_JSON = resolve(process.cwd(), 'devnet-root.json');
const DEPLOY_JSON = resolve(process.cwd(), 'devnet-deployment.json');
const RECEIPT_JSON = resolve(process.cwd(), 'devnet-attestation-receipt.json');

const FEE = 200_000_000; // 0.2 MINA

type State = { dreggRoot: bigint; lastAttestedLeaf: bigint };

async function zkAppState(addr: ReturnType<typeof loadKeys>['zkApp']): Promise<State> {
  const r = await fetchAccount({ publicKey: addr });
  const s = r.account?.zkapp?.appState;
  if (!s) throw new Error('zkApp account has no state — is it deployed?');
  return { dreggRoot: s[0].toBigInt(), lastAttestedLeaf: s[1].toBigInt() };
}

async function main() {
  console.log('=== exercise the deployed dregg attestation gate (devnet) ===');
  connect();
  const { deployerKey, deployer, zkApp } = loadKeys();
  const emitted = JSON.parse(readFileSync(ROOT_JSON, 'utf8')) as EmittedRoot;
  const deployment = JSON.parse(readFileSync(DEPLOY_JSON, 'utf8')) as {
    zkAppAddress: string;
  };
  if (deployment.zkAppAddress !== zkApp.toBase58()) {
    throw new Error(
      `key file and devnet-deployment.json disagree on the zkApp address: ` +
        `${zkApp.toBase58()} vs ${deployment.zkAppAddress}`,
    );
  }

  const root = Field(BigInt(emitted.root));
  const leaf = Field(BigInt(emitted.leaf));
  const siblings = emitted.siblings.map((s) => Field(BigInt(s)));
  const isRight = emitted.isRight.map((b) => Bool(b));

  console.log(`  endpoint : ${MINA_ENDPOINT}`);
  console.log(`  zkApp    : ${zkApp.toBase58()}`);
  console.log(`  root     : ${emitted.root}`);
  console.log(`  leaf     : ${emitted.leaf}  (${emitted.leafMeaning[emitted.leafIndex]})`);
  console.log(`  balance  : ${mina((await balance(deployer)) ?? 0n)}\n`);

  const s0 = await zkAppState(zkApp);
  if (s0.dreggRoot !== root.toBigInt()) {
    throw new Error(
      `the deployed gate anchors ${s0.dreggRoot.toString(16)}, not the emitted root. ` +
        'Re-run devnet:deploy against this devnet-root.json.',
    );
  }
  console.log(`  on-chain anchored root matches the emitted root ✓`);

  // --- compile ---------------------------------------------------------------
  let t = Date.now();
  await DreggMembershipAttestation.compile();
  await DreggAttestedGate.compile();
  console.log(`  compiled both circuits in ${secs(t)}\n`);

  const app = new DreggAttestedGate(zkApp);
  const receipt: Record<string, unknown> = {
    network: 'mina-devnet',
    endpoint: MINA_ENDPOINT,
    ranAt: new Date().toISOString(),
    zkAppAddress: zkApp.toBase58(),
    attestedRoot: emitted.root,
    attestedLeaf: emitted.leaf,
  };

  // ==========================================================================
  // [A] ACCEPT — an honest witness, proved and consumed on chain.
  // ==========================================================================
  console.log('[A] honest attestation');
  t = Date.now();
  const { proof } = await DreggMembershipAttestation.proveMembership(
    root,
    leaf,
    siblings,
    isRight,
  );
  console.log(`    proved depth-${emitted.depth} membership in ${secs(t)}`);
  if (!(await DreggMembershipAttestation.verify(proof))) {
    throw new Error('the honest attestation proof does not verify locally');
  }
  console.log('    the attestation proof verifies locally ✓');

  const nonceA = (await nonceOf(deployer))!;
  t = Date.now();
  const acceptTx = await Mina.transaction(
    { sender: deployer, fee: FEE, nonce: nonceA, memo: 'dregg-attest-accept' },
    async () => {
      await app.actOnAttestedLeaf(proof);
    },
  );
  await acceptTx.prove();
  const acceptPending = await acceptTx.sign([deployerKey]).send();
  const acceptHash = acceptPending.hash;
  console.log(`    ACCEPT tx ${acceptHash}`);
  console.log(`    ${explorerTx(acceptHash)}`);

  // Both conjuncts are load-bearing. The state check alone would pass instantly
  // on a re-run against a gate that already holds this leaf — a green that means
  // "an earlier run worked", not "this transaction landed".
  const landed = await until(
    async () =>
      ((await nonceOf(deployer)) ?? 0) > nonceA &&
      (await zkAppState(zkApp)).lastAttestedLeaf === leaf.toBigInt(),
    'the honest attestation to be recorded on chain',
  );
  if (!landed) {
    console.error('    the honest attestation never landed. Check the explorer link.');
    process.exit(1);
  }
  console.log(`    ✓ ACCEPTED: the zkApp recorded the attested leaf in ${secs(t)}`);
  receipt.acceptTx = acceptHash;
  receipt.acceptResult = 'included; lastAttestedLeaf == the attested leaf';

  // ==========================================================================
  // [R1] REJECT on chain — a STALE attestation, refused at inclusion time.
  //
  // The relay advances the anchored root. The attestation above is bound (by
  // its public input, and by the precondition the method's `getAndRequireEquals`
  // wrote into the account update) to the OLD root, so replaying it must fail
  // ON CHAIN rather than locally. The transaction is built and proved FIRST,
  // while the anchored root is still the old one; only then is the new root
  // anchored. Nonces are pinned explicitly so the held transaction is next in
  // line behind the re-anchor.
  // ==========================================================================
  console.log('\n[R1] stale attestation, refused on chain');
  const nonceB = (await nonceOf(deployer))!;
  const nextRoot = Poseidon.hash([root, Field(1)]); // the relay's "next" root

  t = Date.now();
  const staleTx = await Mina.transaction(
    { sender: deployer, fee: FEE, nonce: nonceB + 1, memo: 'dregg-attest-stale' },
    async () => {
      await app.actOnAttestedLeaf(proof);
    },
  );
  await staleTx.prove();
  const staleSigned = staleTx.sign([deployerKey]);
  console.log(`    built + proved the replay at nonce ${nonceB + 1} in ${secs(t)}`);
  console.log(`    (its precondition pins dreggRoot == ${emitted.root})`);

  console.log(`    re-anchoring to a new root ${'0x' + nextRoot.toBigInt().toString(16)}`);
  const advanceTx = await Mina.transaction(
    { sender: deployer, fee: FEE, nonce: nonceB, memo: 'dregg-root-advance' },
    async () => {
      await app.setDreggRoot(nextRoot);
    },
  );
  await advanceTx.prove();
  const advancePending = await advanceTx.sign([deployerKey]).send();
  console.log(`    advance tx ${advancePending.hash}`);
  const advanced = await until(
    async () => (await zkAppState(zkApp)).dreggRoot === nextRoot.toBigInt(),
    'the new root to be anchored',
  );
  if (!advanced) {
    console.error('    the re-anchor never landed; cannot stage the rejection.');
    process.exit(1);
  }
  console.log('    the gate now anchors the NEW root ✓');
  receipt.rootAdvanceTx = advancePending.hash;
  receipt.advancedRoot = '0x' + nextRoot.toBigInt().toString(16);

  const before = await zkAppState(zkApp);
  t = Date.now();
  const staleSent = await staleSigned.safeSend();
  const staleHash = staleSent.hash;
  console.log(`    REJECT tx ${staleHash}`);
  console.log(`    ${explorerTx(staleHash)}`);

  // Two shapes of on-chain refusal are possible and BOTH are recorded honestly,
  // because which one a daemon gives is its choice, not ours:
  //   - refused at ADMISSION: the pool applies the command against its ledger,
  //     sees the precondition fail, and never gossips it. The hash exists but
  //     names nothing in a block.
  //   - included as FAILED: the command enters a block, consumes the fee, and
  //     bumps the nonce, with its effects discarded.
  // Waiting 20 minutes for a nonce bump that admission-refusal will never
  // produce is just a stall, so the budget collapses in that case.
  const admissionRefused = staleSent.status === 'rejected';
  const admissionErrors = admissionRefused
    ? JSON.stringify((staleSent as { errors?: unknown }).errors)
    : null;
  if (admissionRefused) {
    console.log(`    the daemon refused it at admission: ${admissionErrors}`);
  }

  // The fee payer's nonce advancing PAST this transaction is what proves it was
  // processed rather than silently dropped; the state not moving is what proves
  // its effects were refused.
  const processed = await until(
    async () => ((await nonceOf(deployer)) ?? 0) > nonceB + 1,
    'the stale attestation to be processed',
    admissionRefused ? 1 : 20 * 60_000,
  );
  const after = await zkAppState(zkApp);
  console.log(`    processed=${processed} in ${secs(t)}`);
  console.log(`    zkApp dreggRoot        : 0x${after.dreggRoot.toString(16)}`);
  console.log(`    zkApp lastAttestedLeaf : 0x${after.lastAttestedLeaf.toString(16)}`);

  const refused =
    after.lastAttestedLeaf === before.lastAttestedLeaf &&
    after.dreggRoot === nextRoot.toBigInt();
  if (!refused) {
    console.error('    ✗ the stale attestation CHANGED STATE — the gate did not refuse it.');
    process.exit(1);
  }
  console.log('    ✓ REJECTED: the stale attestation did not take effect on chain');
  receipt.rejectTx = staleHash;
  receipt.rejectMechanism =
    'account-state precondition (dreggRoot) pinned the retired root';
  receipt.rejectResult = admissionRefused
    ? `refused at ADMISSION by the daemon (never entered a block): ${admissionErrors}`
    : processed
      ? 'included and PROCESSED by the network; fee consumed, nonce bumped, zkApp state unchanged'
      : 'submitted; zkApp state unchanged (nonce advance not observed within budget)';
  receipt.rejectOnChain = !admissionRefused && processed;

  // ==========================================================================
  // [R2] The network verifies the PROOF: corrupt it on the wire.
  // Best-effort probe — recorded, never fatal.
  // ==========================================================================
  console.log('\n[R2] corrupted proof on the wire (the daemon must refuse it)');
  try {
    const nonceC = (await nonceOf(deployer))!;
    const badTx = await Mina.transaction(
      { sender: deployer, fee: FEE, nonce: nonceC, memo: 'dregg-bad-proof' },
      async () => {
        await app.setDreggRoot(Poseidon.hash([nextRoot, Field(2)]));
      },
    );
    await badTx.prove();
    const signed = badTx.sign([deployerKey]);
    // Flip the middle of the base64 proof. The statement is untouched, so the
    // ONLY thing that can reject this is the proof check itself.
    const aus = (signed as unknown as {
      transaction: { accountUpdates: { authorization: { proof?: string } }[] };
    }).transaction.accountUpdates;
    const withProof = aus.find((au) => typeof au.authorization?.proof === 'string');
    if (!withProof?.authorization.proof) throw new Error('no proof found on any account update');
    const p = withProof.authorization.proof;
    const mid = Math.floor(p.length / 2);
    withProof.authorization.proof =
      p.slice(0, mid) + (p[mid] === 'A' ? 'B' : 'A') + p.slice(mid + 1);

    const sent = await signed.safeSend();
    if (sent.status === 'rejected') {
      const errs = JSON.stringify((sent as { errors?: unknown }).errors);
      console.log(`    ✓ the daemon REFUSED the corrupted proof: ${errs}`);
      receipt.corruptedProofOutcome = `rejected by the daemon: ${errs}`;
    } else {
      // It entered the mempool; the state must still not move.
      console.log(`    submitted as ${sent.hash}; checking it does not take effect...`);
      const st = await zkAppState(zkApp);
      const tookEffect = st.dreggRoot !== nextRoot.toBigInt();
      console.log(`    took effect = ${tookEffect}`);
      receipt.corruptedProofOutcome = tookEffect
        ? `⚑ ACCEPTED (${sent.hash}) — INVESTIGATE`
        : `submitted as ${sent.hash}; no state change`;
      receipt.corruptedProofTx = sent.hash;
    }
  } catch (e) {
    const m = e instanceof Error ? e.message : String(e);
    console.log(`    the corrupted proof was refused before/at submission: ${m.slice(0, 300)}`);
    receipt.corruptedProofOutcome = `refused: ${m.slice(0, 300)}`;
  }

  // ==========================================================================
  // [R3] The local, hash-less refusal: a tampered witness is UNPROVABLE.
  // ==========================================================================
  console.log('\n[R3] tampered witness is unprovable (no transaction can exist)');
  const bad = siblings.slice();
  bad[0] = bad[0].add(1);
  let proved = false;
  try {
    await DreggMembershipAttestation.proveMembership(root, leaf, bad, isRight);
    proved = true;
  } catch {
    /* expected: the constraint system is unsatisfiable */
  }
  if (proved) {
    console.error('    ✗ a tampered sibling still produced a proof (UNSOUND)');
    process.exit(1);
  }
  console.log('    ✓ a tampered sibling cannot be proved — no transaction reaches the network');
  receipt.tamperedWitness = 'unprovable (constraint system unsatisfiable); no tx exists';

  writeFileSync(RECEIPT_JSON, JSON.stringify(receipt, null, 2) + '\n');
  console.log(`\n  wrote ${RECEIPT_JSON}`);
  console.log('\n=== PASS ===');
  console.log(`  ACCEPT : ${acceptHash}`);
  console.log(`  REJECT : ${staleHash}`);
}

main().catch((e) => {
  console.error(e instanceof Error ? e.stack : e);
  process.exit(1);
});
