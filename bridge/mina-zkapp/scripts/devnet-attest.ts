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
//   [R2] the PROOF ITSELF — the daemon refuses the command outright (no hash;
//        it never enters a block). This splits in two, and the split is the
//        point: [R2a] corrupting the proof's ENCODING is refused at DECODE,
//        before any cryptography runs, and demonstrates nothing about
//        verification; [R2b] moving a VALID proof onto a different account
//        update leaves the bytes well-formed and only the STATEMENT wrong, so
//        only the verification equation can refuse it — and the same bytes are
//        then submitted on their own account update and accepted, as a control.
//
// All are exercised below. Claiming more than this — e.g. that the chain
// "caught a forged Merkle path" — would be false: the prover caught it first.
// ---------------------------------------------------------------------------

import { Bool, Field, Mina, Poseidon, fetchAccount } from 'o1js';
import { readFileSync, writeFileSync } from 'node:fs';
import { resolve } from 'node:path';
import {
  DreggAttestedGate,
  DreggMembershipAttestation,
  signAnchor,
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
  const { deployerKey, deployer, zkApp, relayKey } = loadKeys();
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
  const advanceAuth = signAnchor(relayKey, root, nextRoot);
  const advanceTx = await Mina.transaction(
    { sender: deployer, fee: FEE, nonce: nonceB, memo: 'dregg-root-advance' },
    async () => {
      await app.setDreggRoot(nextRoot, advanceAuth);
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
  // [R2] The network verifies the PROOF ITSELF. Two probes, and the difference
  // between them is the whole point.
  //
  // [R2a] CORRUPTED ENCODING. Flip a character in the serialised proof. This is
  //       what an earlier version of this script did and called a proof-check
  //       demonstration. It is not one: the daemon answers `Invalid rich
  //       scalar: Proof …`, which is a DECODE failure — it never reached the
  //       verifier. Kept, labelled as what it is, as the contrast case.
  //
  // [R2b] WELL-FORMED PROOF, WRONG STATEMENT. Build TWO valid `setDreggRoot`
  //       transactions and move the proof of one onto the account update of the
  //       other. Mina's transaction commitment covers account-update BODIES,
  //       not authorisations, so the fee-payer signature stays valid and the
  //       bytes stay a perfectly well-formed Pickles proof — it simply attests
  //       a different account update. Nothing can reject it except the
  //       verification equation.
  //
  //       The CONTROL is what makes this readable: after the spliced command is
  //       refused, the same proof bytes are submitted on their OWN account
  //       update and must be ACCEPTED by the same daemon in the same minute.
  //       Rejected-then-accepted, one variable changed, and the variable is the
  //       statement.
  // ==========================================================================
  type ProofAu = { authorization: { proof?: string } };
  const proofOf = (signed: unknown): ProofAu => {
    const aus = (signed as { transaction: { accountUpdates: ProofAu[] } }).transaction
      .accountUpdates;
    const au = aus.find((a) => typeof a.authorization?.proof === 'string');
    if (!au?.authorization.proof) throw new Error('no proof on any account update');
    return au;
  };
  /**
   * Did the daemon refuse this at DECODE time or at VERIFICATION time? The
   * distinction is the defect this section exists to fix, so it is classified
   * from the daemon's own words rather than asserted.
   *
   * ⚑ ONE OF THOSE WORDS IS NOT THE DAEMON'S. o1js rewrites the daemon's
   * verdict before you ever see it: `dist/node/lib/mina/v1/errors.js` carries
   *
   *   { pattern: /\(invalid \(Invalid_proof \\"In progress\\"\)\)/g,
   *     replacement: 'Stale verification key detected. Please make sure that
   *                   deployed verification key reflects latest zkApp changes.' }
   *
   * so `Invalid_proof` — the network saying THIS PROOF DOES NOT VERIFY — reaches
   * the operator as a hint that they forgot to redeploy. That guess is usually
   * right and here it is exactly wrong: the verification key is current, and the
   * control transaction below proves it by being accepted against the same key
   * with the same proof bytes minutes later. The string is matched here so the
   * receipt records a proof-verification refusal as a proof-verification
   * refusal, and says whose wording it is.
   */
  const classify = (errs: string): 'parse' | 'verification' | 'other' => {
    const e = errs.toLowerCase();
    if (e.includes('rich scalar') || e.includes('could not decode') || e.includes('base64'))
      return 'parse';
    if (
      e.includes('invalid_proof') ||
      e.includes('stale verification key') || // o1js's rewrite of Invalid_proof
      e.includes('verification_failed')
    )
      return 'verification';
    if (e.includes('proof')) return 'other';
    return 'other';
  };

  console.log('\n[R2a] corrupted proof ENCODING (expected: refused at DECODE, not verification)');
  try {
    const nonceC = (await nonceOf(deployer))!;
    const badRoot = Poseidon.hash([nextRoot, Field(2)]);
    const badTx = await Mina.transaction(
      { sender: deployer, fee: FEE, nonce: nonceC, memo: 'dregg-bad-proof' },
      async () => {
        await app.setDreggRoot(badRoot, signAnchor(relayKey, nextRoot, badRoot));
      },
    );
    await badTx.prove();
    const signed = badTx.sign([deployerKey]);
    const au = proofOf(signed);
    const p = au.authorization.proof!;
    const mid = Math.floor(p.length / 2);
    au.authorization.proof = p.slice(0, mid) + (p[mid] === 'A' ? 'B' : 'A') + p.slice(mid + 1);

    const sent = await signed.safeSend();
    if (sent.status === 'rejected') {
      const errs = JSON.stringify((sent as { errors?: unknown }).errors);
      const how = classify(errs);
      console.log(`    the daemon refused it (${how}): ${errs}`);
      receipt.corruptedEncodingOutcome = `rejected by the daemon [${how}]: ${errs}`;
      receipt.corruptedEncodingRefusedAt = how;
    } else {
      console.log(`    submitted as ${sent.hash}; checking it does not take effect...`);
      const st = await zkAppState(zkApp);
      const tookEffect = st.dreggRoot !== nextRoot.toBigInt();
      receipt.corruptedEncodingOutcome = tookEffect
        ? `⚑ ACCEPTED (${sent.hash}) — INVESTIGATE`
        : `submitted as ${sent.hash}; no state change`;
      receipt.corruptedEncodingTx = sent.hash;
    }
  } catch (e) {
    const m = e instanceof Error ? e.message : String(e);
    console.log(`    refused before/at submission: ${m.slice(0, 300)}`);
    receipt.corruptedEncodingOutcome = `refused: ${m.slice(0, 300)}`;
  }

  console.log(
    '\n[R2b] WELL-FORMED proof of a DIFFERENT statement (expected: refused at VERIFICATION)',
  );
  try {
    const nonceD = (await nonceOf(deployer))!;
    const rootX = Poseidon.hash([nextRoot, Field(3)]);
    const rootY = Poseidon.hash([nextRoot, Field(4)]);

    // Two independently valid commands, at the SAME nonce so that at most one
    // of them can ever take effect.
    const txX = await Mina.transaction(
      { sender: deployer, fee: FEE, nonce: nonceD, memo: 'dregg-splice-control' },
      async () => {
        await app.setDreggRoot(rootX, signAnchor(relayKey, nextRoot, rootX));
      },
    );
    await txX.prove();
    const signedX = txX.sign([deployerKey]);

    const txY = await Mina.transaction(
      { sender: deployer, fee: FEE, nonce: nonceD, memo: 'dregg-splice-forged' },
      async () => {
        await app.setDreggRoot(rootY, signAnchor(relayKey, nextRoot, rootY));
      },
    );
    await txY.prove();
    const signedY = txY.sign([deployerKey]);

    const proofX = proofOf(signedX).authorization.proof!;
    const auY = proofOf(signedY);
    // The splice. `proofX` is untouched — every byte is a proof the prover
    // itself produced and the daemon will accept below.
    auY.authorization.proof = proofX;
    console.log(`    spliced proof-of-X (${proofX.length} b64 chars) onto the update that sets Y`);

    const sentForged = await signedY.safeSend();
    let forgedVerdict: string;
    let forgedHow: string;
    if (sentForged.status === 'rejected') {
      const errs = JSON.stringify((sentForged as { errors?: unknown }).errors);
      forgedHow = classify(errs);
      forgedVerdict = `rejected by the daemon [${forgedHow}]: ${errs}`;
      console.log(`    the daemon refused the spliced command (${forgedHow}): ${errs}`);
    } else {
      console.log(`    entered the pool as ${sentForged.hash}; checking it takes no effect...`);
      const st = await zkAppState(zkApp);
      forgedHow = st.dreggRoot === rootY.toBigInt() ? 'ACCEPTED' : 'no-effect';
      forgedVerdict =
        forgedHow === 'ACCEPTED'
          ? `⚑ ACCEPTED (${sentForged.hash}) — INVESTIGATE, this would be a soundness failure`
          : `submitted as ${sentForged.hash}; no state change`;
    }
    receipt.splicedProofOutcome = forgedVerdict;
    receipt.splicedProofRefusedAt = forgedHow;

    // --- the control: the SAME bytes, on their own statement ----------------
    const sentControl = await signedX.safeSend();
    console.log(`    control tx (same proof, its own account update) ${sentControl.hash}`);
    console.log(`    ${explorerTx(sentControl.hash)}`);
    const controlLanded = await until(
      async () => (await zkAppState(zkApp)).dreggRoot === rootX.toBigInt(),
      'the control command (identical proof bytes) to be applied',
      10 * 60_000,
    );
    console.log(
      controlLanded
        ? '    ✓ CONTROL APPLIED: the identical proof bytes were accepted on their own statement'
        : '    the control did not land within budget — the splice result stands alone',
    );
    receipt.splicedProofControlTx = sentControl.hash;
    receipt.splicedProofControlApplied = controlLanded;
    receipt.splicedProofReading = controlLanded
      ? 'the same proof bytes were REFUSED on a different account update and APPLIED on their own; ' +
        'the only variable was the statement, so the refusal is a verification failure, not a decode failure'
      : 'the spliced command was refused; the control did not land in budget, so the ' +
        'rejected-then-accepted pairing is NOT established by this run';
  } catch (e) {
    const m = e instanceof Error ? e.message : String(e);
    console.log(`    the splice probe failed before it could conclude: ${m.slice(0, 300)}`);
    receipt.splicedProofOutcome = `inconclusive: ${m.slice(0, 300)}`;
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
