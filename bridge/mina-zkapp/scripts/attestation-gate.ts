// The dregg <-> Mina Poseidon-attestation GATE.
//
// This is the runnable form of the "mutual proof" step: Mina verifies, IN
// CIRCUIT, a Poseidon-Merkle path into a Pasta root the dregg-side Rust hasher
// produced. It runs entirely from committed sources — `src/` is compiled by
// `tsc` and this driver imports the emitted JS, so a type error or a divergence
// in the library code fails the gate rather than living in a scratch dir.
//
//   npm run gate            (= npm run build && node dist/scripts/attestation-gate.js)
//
// It performs four demonstrations, ALL of which must pass:
//
//   [1] CROSS-IMPLEMENTATION AGREEMENT. o1js `Poseidon.hash` reproduces every
//       Mina-Poseidon vector the Rust probe asserts (9 digests + a depth-2
//       Merkle root + the field modulus), bit-for-bit.
//   [2] IN-CIRCUIT MERKLE PATH. A `ZkProgram` verifies a Poseidon-Merkle
//       authentication path whose public input is the Rust-emitted root.
//   [3] COMPILE + PROVE + VERIFY. Real Pickles proving, real verification, and
//       the proof-carrying public output is the opened leaf.
//   [4] TAMPERED-WITNESS REJECTION. A wrong sibling must FAIL to prove.
//
//   [5] (composition) the zkApp `DreggAttestedGate` deploys on a local chain
//       and consumes the attestation proof — so the claim "a Mina zkApp
//       verified a dregg commitment" names something that actually ran.
//   [6] AUTHORIZATION. `setDreggRoot` is relay-authorized because the circuit
//       asserts a relay signature over the exact transition — a non-relay
//       signer, an empty signature and a signature for another transition are
//       each refused. The first two would have passed against the earlier
//       contract, whose "relay-authorized" comment checked nothing.
//   [7] PARSE vs VERIFY. A well-formed proof carrying a statement its prover
//       had no witness for parses cleanly and FAILS VERIFICATION — shown both
//       at the `ZkProgram` level and by moving a proof between two signed
//       account updates, with the same bytes accepted on their own update as
//       the control. A damaged encoding is refused at DECODE, separately, so
//       the two events cannot be mistaken for each other.
//
// NO PART OF THIS SKIPS. Absent o1js, an unsupported Node, or a mismatched
// vector are all hard failures.
//
// TOOLCHAIN, pinned and load-bearing: o1js 2.15.0 on Node >= 20. The repo's
// previous pin (o1js ^1.0.0, resolving to 1.9.1) is NOT usable: its prover
// bindings abort inside Poseidon absorb during `compile()` on Node >= 26, and
// its `ZkProgram` method types reject the committed source (`tsc` fails).

import { Field, Poseidon, Bool, Mina, AccountUpdate, PrivateKey, Signature } from 'o1js';
import {
  ATTEST_DEPTH,
  DreggMembershipAttestation,
  DreggAttestationProof,
  DreggAttestedGate,
  makeDreggMembershipAttestation,
  compress,
  signAnchor,
  sparsePath,
} from '../src/DreggPoseidonAttestation.js';
import {
  PASTA_FP_MODULUS_HEX,
  RUST_GOLD_HASHES,
  RUST_MERKLE_ROOT_1234,
  RUST_MERKLE_LEAVES_1234,
  goldInputs,
  fpHex,
} from '../src/rust-gold-vectors.js';

/** The o1js the gate is PINNED to. `package.json` pins the same string exactly
 *  (no caret); a resolved tree that disagrees is a gate failure, not a warning. */
const PINNED_O1JS = '2.15.0';
/** o1js 1.9.1's prover bindings abort during `compile()` on Node >= 26. This pin
 *  is what makes the gate runnable on a current Node at all. */
const MIN_NODE_MAJOR = 20;

function ok(msg: string) {
  console.log('  ✓ ' + msg);
}
/** Fail-fast: the gate is all-must-pass, so the first red ends the run. */
function fail(msg: string): never {
  console.error('  ✗ ' + msg);
  throw new Error(msg);
}
function check(cond: boolean, good: string, bad: string) {
  if (cond) ok(good);
  else fail(bad);
}
const secs = (t: number) => ((Date.now() - t) / 1000).toFixed(1) + 's';

// ---------------------------------------------------------------------------

async function main() {
  console.log('=== dregg <-> Mina Poseidon-attestation gate ===');
  const o1js = await o1jsVersion();
  console.log(`    node ${process.version}, o1js ${o1js}\n`);

  console.log('[0] toolchain pin');
  const nodeMajor = Number(process.version.replace(/^v/, '').split('.')[0]);
  check(
    nodeMajor >= MIN_NODE_MAJOR,
    `node ${process.version} >= ${MIN_NODE_MAJOR}`,
    `node ${process.version} is below the supported floor v${MIN_NODE_MAJOR}`,
  );
  check(
    o1js === PINNED_O1JS,
    `o1js resolves to the pin ${PINNED_O1JS}`,
    `o1js resolved to ${o1js}, not the pinned ${PINNED_O1JS}`,
  );

  // -----------------------------------------------------------------------
  // [1] Cross-implementation agreement, Rust `mina_poseidon_hash` <-> o1js.
  // -----------------------------------------------------------------------
  console.log('[1] cross-implementation agreement (Rust mina-poseidon <-> o1js)');

  const modulusHex = '0x' + Field.ORDER.toString(16).padStart(64, '0');
  check(
    modulusHex === PASTA_FP_MODULUS_HEX,
    'Pasta Fp modulus agrees with the Rust probe',
    `field modulus differs: o1js ${modulusHex} vs rust ${PASTA_FP_MODULUS_HEX}`,
  );

  let hashMismatches = 0;
  for (const c of RUST_GOLD_HASHES) {
    const got = fpHex(Poseidon.hash(goldInputs(c)));
    if (got !== c.digest) {
      fail(`KAT '${c.name}': o1js ${got} != rust ${c.digest}`);
      hashMismatches++;
    }
  }
  check(
    hashMismatches === 0,
    `all ${RUST_GOLD_HASHES.length} Mina-Poseidon digests agree bit-for-bit`,
    `${hashMismatches} of ${RUST_GOLD_HASHES.length} digests diverged`,
  );

  // Rebuild the probe's depth-2 tree with the SAME `compress` the circuit uses.
  const leaves = RUST_MERKLE_LEAVES_1234.map((x) => Field(x));
  const n01 = compress(leaves[0], leaves[1]);
  const n23 = compress(leaves[2], leaves[3]);
  const goldRoot = compress(n01, n23);
  check(
    goldRoot.toBigInt() === RUST_MERKLE_ROOT_1234,
    `depth-2 Merkle root agrees: ${fpHex(goldRoot)}`,
    `depth-2 root diverged: o1js ${fpHex(goldRoot)} != rust 0x${RUST_MERKLE_ROOT_1234.toString(16).padStart(64, '0')}`,
  );

  // Reject polarity: the vector table is not vacuously satisfiable.
  check(
    fpHex(Poseidon.hash([Field(0), Field(1), Field(3)])) !==
      RUST_GOLD_HASHES.find((c) => c.name === 'seq012')!.digest,
    'tampered input does NOT reproduce a gold digest (vectors are discriminating)',
    'a tampered input reproduced a gold digest',
  );

  // -----------------------------------------------------------------------
  // [2]+[3] In-circuit path into the Rust-emitted root, compiled and proved.
  //
  // Two shapes are exercised:
  //   (a) depth-2, public input = the Rust-emitted root VERBATIM. This is the
  //       direct claim: the circuit's own recomputation must land on the value
  //       Rust produced or the proof does not exist.
  //   (b) depth-32 (ATTEST_DEPTH, the dregg cell-tree depth), which is the
  //       program the zkApp composes with in [5].
  // -----------------------------------------------------------------------
  console.log('\n[2] in-circuit Poseidon-Merkle path, depth 2, into the Rust root');
  const d2 = makeDreggMembershipAttestation(2);
  const cs2 = await d2.analyzeMethods();
  console.log(
    `    circuit: ${cs2.proveMembership.rows} rows (${cs2.proveMembership.gates.length} gates)`,
  );

  let t = Date.now();
  await d2.compile();
  ok(`compiled depth-2 attestation in ${secs(t)}`);

  // leaf 3 sits at index 2: level-0 sibling is 4 (current is LEFT), level-1
  // sibling is n01 (current is RIGHT).
  const leaf = Field(3);
  const sibs2 = [Field(4), n01];
  const isRight2 = [Bool(false), Bool(true)];

  console.log('\n[3] prove + verify');
  t = Date.now();
  const { proof: p2 } = await d2.proveMembership(goldRoot, leaf, sibs2, isRight2);
  ok(`proved membership of leaf 3 under the Rust root in ${secs(t)}`);

  check(await d2.verify(p2), 'the proof VERIFIES', 'the proof failed to verify');
  check(
    p2.publicInput.toBigInt() === RUST_MERKLE_ROOT_1234,
    'the proof is bound to the Rust-emitted root (public input)',
    'the proof public input is not the Rust root',
  );
  check(
    p2.publicOutput.toBigInt() === 3n,
    'proof-carrying public output == 3, the opened leaf',
    'the public output is not the opened leaf',
  );

  // -----------------------------------------------------------------------
  // [4] Soundness polarity: a tampered witness must not prove.
  // -----------------------------------------------------------------------
  console.log('\n[4] tampered-witness rejection');
  let tamperedProved = false;
  try {
    await d2.proveMembership(goldRoot, leaf, [Field(999), n01], isRight2);
    tamperedProved = true;
  } catch {
    /* expected: the constraint system is unsatisfiable */
  }
  check(
    !tamperedProved,
    'a wrong sibling is rejected at proving time',
    'a tampered witness still produced a proof (UNSOUND)',
  );

  let tamperedRootProved = false;
  try {
    await d2.proveMembership(goldRoot.add(1), leaf, sibs2, isRight2);
    tamperedRootProved = true;
  } catch {
    /* expected */
  }
  check(
    !tamperedRootProved,
    'a wrong public root is rejected at proving time',
    'a tampered root still produced a proof (UNSOUND)',
  );

  // -----------------------------------------------------------------------
  // [5] The zkApp composition, at the real cell-tree depth.
  // -----------------------------------------------------------------------
  console.log(`\n[5] zkApp composition at ATTEST_DEPTH=${ATTEST_DEPTH}`);

  const { path, nodes, root: deepRoot } = sparsePath(leaves, 2, ATTEST_DEPTH);
  check(
    nodes[1].toBigInt() === RUST_MERKLE_ROOT_1234,
    'the depth-32 path passes through the Rust-emitted depth-2 root',
    'the depth-32 path does not pass through the Rust root',
  );

  const csDeep = await DreggMembershipAttestation.analyzeMethods();
  console.log(`    attestation circuit: ${csDeep.proveMembership.rows} rows`);

  t = Date.now();
  await DreggMembershipAttestation.compile();
  ok(`compiled depth-${ATTEST_DEPTH} attestation in ${secs(t)}`);

  t = Date.now();
  const { proof: pDeep } = await DreggMembershipAttestation.proveMembership(
    deepRoot,
    leaf,
    path.siblings,
    path.isRight,
  );
  ok(`proved depth-${ATTEST_DEPTH} membership in ${secs(t)}`);
  check(
    await DreggMembershipAttestation.verify(pDeep),
    'the depth-32 proof VERIFIES',
    'the depth-32 proof failed to verify',
  );

  const gateAnalysis = await DreggAttestedGate.analyzeMethods();
  console.log(
    `    zkApp actOnAttestedLeaf: ${gateAnalysis.actOnAttestedLeaf.rows} rows` +
      ` (verifies the attestation proof recursively)`,
  );

  t = Date.now();
  await DreggAttestedGate.compile();
  ok(`compiled the DreggAttestedGate zkApp in ${secs(t)}`);

  const Local = await Mina.LocalBlockchain({ proofsEnabled: true });
  Mina.setActiveInstance(Local);
  const deployer = Local.testAccounts[0];
  const zkAppKey = PrivateKey.random();
  const zkAppAddress = zkAppKey.toPublicKey();
  const zkApp = new DreggAttestedGate(zkAppAddress);
  // The relay is a THIRD key: not the deployer, not the zkApp account. Only it
  // can move the anchored root, and [6] below is where that is tested.
  const relayKey = PrivateKey.random();
  const relay = relayKey.toPublicKey();

  t = Date.now();
  const deployTx = await Mina.transaction(deployer, async () => {
    AccountUpdate.fundNewAccount(deployer);
    await zkApp.deploy({ relay });
  });
  await deployTx.prove();
  await deployTx.sign([deployer.key, zkAppKey]).send();
  ok(`deployed the zkApp in ${secs(t)}`);
  check(
    zkApp.relay.get().toBase58() === relay.toBase58(),
    'the deploy installed the relay key in state (the anchor has a named authority)',
    'the deployed gate does not hold the relay key',
  );

  t = Date.now();
  const anchorTx = await Mina.transaction(deployer, async () => {
    await zkApp.setDreggRoot(deepRoot, signAnchor(relayKey, Field(0), deepRoot));
  });
  await anchorTx.prove();
  await anchorTx.sign([deployer.key]).send();
  check(
    zkApp.dreggRoot.get().toBigInt() === deepRoot.toBigInt(),
    `zkApp anchored the root in ${secs(t)}`,
    'zkApp did not anchor the root',
  );

  t = Date.now();
  const actTx = await Mina.transaction(deployer, async () => {
    await zkApp.actOnAttestedLeaf(pDeep);
  });
  await actTx.prove();
  await actTx.sign([deployer.key]).send();
  check(
    zkApp.lastAttestedLeaf.get().toBigInt() === 3n,
    `the zkApp CONSUMED the attestation proof and recorded leaf 3 in ${secs(t)}`,
    'the zkApp did not record the attested leaf',
  );

  // The zkApp must refuse a proof bound to a different root.
  const { proof: otherProof } = await DreggMembershipAttestation.proveMembership(
    sparsePath([Field(7), Field(8)], 0, ATTEST_DEPTH).root,
    Field(7),
    sparsePath([Field(7), Field(8)], 0, ATTEST_DEPTH).path.siblings,
    sparsePath([Field(7), Field(8)], 0, ATTEST_DEPTH).path.isRight,
  );
  let wrongRootAccepted = false;
  try {
    const badTx = await Mina.transaction(deployer, async () => {
      await zkApp.actOnAttestedLeaf(otherProof);
    });
    await badTx.prove();
    await badTx.sign([deployer.key]).send();
    wrongRootAccepted = true;
  } catch {
    /* expected: publicInput.assertEquals(root) fails */
  }
  check(
    !wrongRootAccepted,
    'the zkApp REFUSES an attestation bound to a different root',
    'the zkApp accepted an attestation bound to a different root (UNSOUND)',
  );

  // -----------------------------------------------------------------------
  // [6] The root anchor is AUTHORIZED, and the authorization is a condition
  //     the circuit asserts.
  //
  //     The previous shape of this contract took `setDreggRoot(newRoot)` with
  //     an empty body and a comment reading "relay-authorized". Under the
  //     default `proof` permission that is open to everyone: producing a proof
  //     of an unconditional method is exactly what any caller can do. These
  //     three checks are what make the comment true — and the first two are
  //     the ones that would have gone green against the old contract, which is
  //     why they are here rather than a note in the doc.
  // -----------------------------------------------------------------------
  console.log('\n[6] the anchor is relay-authorized (the code checks what the comment says)');
  const nextRoot = Poseidon.hash([deepRoot, Field(1)]);

  const anchorRefusal = async (label: string, build: () => Promise<void>) => {
    let accepted = false;
    let message = '';
    try {
      const tx = await Mina.transaction(deployer, build);
      await tx.prove();
      await tx.sign([deployer.key]).send();
      accepted = true;
    } catch (e) {
      message = e instanceof Error ? e.message : String(e);
    }
    check(
      !accepted,
      `${label} — refused (${message.split('\n')[0].slice(0, 60)})`,
      `${label} — ACCEPTED; the anchor is not authorized`,
    );
  };

  await anchorRefusal('an anchor signed by a NON-relay key', async () => {
    await zkApp.setDreggRoot(nextRoot, signAnchor(PrivateKey.random(), deepRoot, nextRoot));
  });
  await anchorRefusal('an anchor carrying NO signature at all', async () => {
    await zkApp.setDreggRoot(nextRoot, Signature.empty());
  });
  await anchorRefusal('a relay signature for a DIFFERENT transition', async () => {
    await zkApp.setDreggRoot(nextRoot, signAnchor(relayKey, deepRoot, Poseidon.hash([nextRoot])));
  });

  // -----------------------------------------------------------------------
  // [7] A WELL-FORMED proof of a statement it does not prove is refused by
  //     VERIFICATION, not by the parser.
  //
  //     The devnet run flipped a character in a serialised proof and got
  //     `Invalid rich scalar: Proof …` — a DECODE failure that never reached
  //     the verifier, and therefore no evidence about verification at all.
  //     Here the two events are produced side by side so they cannot be
  //     confused:
  //       (a) an untouched proof round-trips through JSON and VERIFIES;
  //       (b) the SAME proof bytes carrying a different public input parse
  //           cleanly and FAIL TO VERIFY;
  //       (c) a damaged encoding does not parse at all.
  //     (b) minus (a) isolates the statement as the only variable.
  //
  //     ⚑ Stated exactly: the spliced statement is one for which no witness is
  //     known — leaf 3 opening under the root of a tree built from [7, 8].
  //     Nothing here proves that no such path EXISTS; that would be a Poseidon
  //     preimage claim. What is shown is the soundness-relevant direction: the
  //     verifier does not accept a proof whose prover had no witness for the
  //     statement it is attached to.
  // -----------------------------------------------------------------------
  console.log('\n[7] a well-formed proof of a different statement fails VERIFICATION');
  const foreignRoot = sparsePath([Field(7), Field(8)], 0, ATTEST_DEPTH).root;
  const honestJson = pDeep.toJSON();

  const roundTripped = await DreggAttestationProof.fromJSON(honestJson);
  check(
    await DreggMembershipAttestation.verify(roundTripped),
    '(a) the untouched proof round-trips through JSON and VERIFIES',
    'the untouched proof did not survive a JSON round-trip',
  );

  const splicedJson = { ...honestJson, publicInput: [foreignRoot.toString()] };
  const spliced = await DreggAttestationProof.fromJSON(splicedJson);
  check(
    spliced.publicInput.toBigInt() === foreignRoot.toBigInt() &&
      spliced.publicOutput.toBigInt() === 3n,
    '(b) the spliced proof PARSES — same bytes, statement now (foreign root, leaf 3)',
    'the spliced proof did not decode, so this says nothing about verification',
  );
  check(
    (await DreggMembershipAttestation.verify(spliced)) === false,
    '(b) …and the verifier REJECTS it — a verification failure, not a parse failure',
    'a proof of a statement nobody had a witness for VERIFIED (UNSOUND)',
  );

  // (c) the contrast case: damage the encoding and it never reaches the
  // verifier. Truncation rather than a character flip because it fails to
  // decode deterministically; the devnet run's flipped character is the same
  // event with a less predictable trigger.
  const brokenJson = { ...honestJson, proof: honestJson.proof.slice(0, -16) };
  let brokenParsed = false;
  let brokenError = '';
  try {
    await DreggAttestationProof.fromJSON(brokenJson);
    brokenParsed = true;
  } catch (e) {
    brokenError = (e instanceof Error ? e.message : String(e)).split('\n')[0];
  }
  check(
    !brokenParsed,
    `(c) a damaged encoding is refused at DECODE, before verification (${brokenError.slice(0, 48)})`,
    'a truncated proof encoding still decoded',
  );

  // --- the same experiment one level up: on account updates, on a chain -----
  // `verifyAccountUpdate` is the local chain's implementation of what a daemon
  // does. Mina's transaction commitment covers account-update BODIES and not
  // authorisations, so a proof can be moved between two signed transactions
  // without disturbing anything else — which makes the statement the only
  // difference between the refusal and the acceptance below.
  console.log('    the same, on account updates:');
  const rootX = Poseidon.hash([deepRoot, Field(3)]);
  const rootY = Poseidon.hash([deepRoot, Field(4)]);
  const txX = await Mina.transaction(deployer, async () => {
    await zkApp.setDreggRoot(rootX, signAnchor(relayKey, deepRoot, rootX));
  });
  await txX.prove();
  const signedX = txX.sign([deployer.key]);
  const txY = await Mina.transaction(deployer, async () => {
    await zkApp.setDreggRoot(rootY, signAnchor(relayKey, deepRoot, rootY));
  });
  await txY.prove();
  const signedY = txY.sign([deployer.key]);

  type ProofAu = { authorization: { proof?: string } };
  const proofAu = (signed: unknown): ProofAu => {
    const aus = (signed as { transaction: { accountUpdates: ProofAu[] } }).transaction
      .accountUpdates;
    const au = aus.find((a) => typeof a.authorization?.proof === 'string');
    if (!au?.authorization.proof) fail('no proof found on any account update');
    return au!;
  };
  const proofX = proofAu(signedX).authorization.proof!;
  proofAu(signedY).authorization.proof = proofX;

  let splicedAuAccepted = false;
  let splicedAuError = '';
  try {
    await signedY.send();
    splicedAuAccepted = true;
  } catch (e) {
    splicedAuError = e instanceof Error ? e.message : String(e);
  }
  check(
    !splicedAuAccepted && /Invalid proof for account update/.test(splicedAuError),
    'a valid proof moved onto a DIFFERENT account update is refused as an invalid PROOF',
    splicedAuAccepted
      ? 'the chain accepted a proof of a different account update (UNSOUND)'
      : `refused, but not as a proof failure: ${splicedAuError.split('\n')[0].slice(0, 90)}`,
  );

  await signedX.send();
  check(
    zkApp.dreggRoot.get().toBigInt() === rootX.toBigInt(),
    'CONTROL: the identical proof bytes are ACCEPTED on their own account update',
    'the control transaction did not apply, so the refusal above is not attributable to the statement',
  );
}

async function o1jsVersion(): Promise<string> {
  const { readFile } = await import('node:fs/promises');
  const url = new URL('../../node_modules/o1js/package.json', import.meta.url);
  return JSON.parse(await readFile(url, 'utf8')).version;
}

main()
  .then(() => {
    console.log(
      '\n=== PASS === (a Mina zkApp consumed an in-circuit proof of a' +
        ' Poseidon-Merkle path into a root the dregg-side Rust hasher produced)\n',
    );
  })
  .catch((e) => {
    console.error(e instanceof Error ? e.message : e);
    console.error('\n=== FAILED ===\n');
    process.exit(1);
  });
