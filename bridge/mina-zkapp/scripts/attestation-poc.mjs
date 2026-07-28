// PoC: the minimal MUTUAL-PROOF step across two proof systems (dregg <-> Mina).
//
// The novel direction is "Mina verifies dregg." Verifying dregg's REAL proof
// (a gnark Groth16 on BN254) inside a Mina/Kimchi (Pasta/IPA) zkApp is
// infeasible today: Kimchi has NO pairing gate, and emulating a BN254 pairing
// out of ForeignFieldMul is orders of magnitude past the 2^16-row step ceiling
// (see docs/MINA-DREGG-ZKAPP-BRIDGE.md). The TRACTABLE mutual step is a
// hash-attestation over the ONE primitive both systems compute bit-for-bit:
// Mina-Poseidon over Pasta Fp.
//
// This program does, IN-CIRCUIT on the Mina side, what the existing
// DreggFederation.verifyMembership only STUBBED (it compared roots; it never
// walked a path): it verifies a Poseidon Merkle path into a dregg-emitted Pasta
// root and returns the opened leaf as a proof-carrying public output.
//
// The cross-SYSTEM handshake: the root it checks against
//   0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777
// is the LIVE output of the Rust dregg-side hasher
//   circuit-prove/sketches/mina-pasta-hash-probe  (mina_poseidon_hash, o1-labs
//   mina-poseidon, kimchi params) -> "merkle_root_1234 = 0x0f82...b777".
// So: Rust (dregg's Poseidon) PRODUCES the root; o1js (Mina's proof system)
// PROVES membership under it in-circuit. Two languages, two proof systems, one
// shared commitment.
//
// Run: node scripts/attestation-poc.mjs   (from bridge/mina-zkapp/)
//
// RUNTIME: verified green with o1js 2.15.0 on Node v26 (compile 8.1s, prove
// 7.3s, verify true, tamper rejects). The project's pinned o1js 1.9.1 prover
// bindings crash on Node >=26 (an OCaml-bindings/Node incompat inside
// Poseidon absorb during compile) — run this on Node 20-22 with the pinned
// 1.9.1, or on Node 26 with `npm i o1js@2`. The Poseidon HASHING path (step 1,
// the cross-system root agreement) runs on any supported Node.

import { ZkProgram, Field, Poseidon, Provable, Bool } from 'o1js';

// The depth-2 gold tree over leaves [1,2,3,4], nodes = Poseidon.hash([l,r]).
const DEPTH = 2;

// The root the RUST dregg-side hasher produced (pasted from the probe's live
// stdout, and asserted below to equal o1js's own recomputation).
const RUST_GOLD_ROOT =
  0x0f82b06f11a6dea422082c77668f6ac9fd97a5f21b81525cb61a46c335bbb777n;

// ---------------------------------------------------------------------------
// The Mina-side verifier: a Poseidon Merkle-path attestation of a dregg root.
// ---------------------------------------------------------------------------
const DreggMembershipAttestation = ZkProgram({
  name: 'dregg-membership-attestation',
  publicInput: Field, //  the dregg-emitted Pasta state root
  publicOutput: Field, // the leaf proven to be committed under that root
  methods: {
    proveMembership: {
      privateInputs: [
        Field, //                       the leaf value (private witness)
        Provable.Array(Field, DEPTH), // sibling hashes bottom-up
        Provable.Array(Bool, DEPTH), //  currentIsRightChild at each level
      ],
      async method(dreggRoot, leaf, siblings, currentIsRight) {
        let current = leaf;
        for (let i = 0; i < DEPTH; i++) {
          // If `current` is the right child, the sibling is on the left.
          const left = Provable.if(currentIsRight[i], siblings[i], current);
          const right = Provable.if(currentIsRight[i], current, siblings[i]);
          current = Poseidon.hash([left, right]); // == Rust compress(l, r)
        }
        // The reconstructed root MUST equal the dregg-emitted root.
        current.assertEquals(dreggRoot);
        // Proof-carrying output: this leaf is committed under the dregg root.
        return { publicOutput: leaf };
      },
    },
  },
});

function ok(msg) {
  console.log('  ✓ ' + msg);
}
function fail(msg) {
  console.error('  ✗ ' + msg);
  process.exitCode = 1;
}

async function main() {
  console.log('=== dregg <-> Mina Poseidon-attestation PoC ===\n');

  // 1) Build the same depth-2 tree the Rust probe built, in o1js.
  const L = [1, 2, 3, 4].map((x) => Field(x));
  const n01 = Poseidon.hash([L[0], L[1]]); // compress(1,2)
  const n23 = Poseidon.hash([L[2], L[3]]); // compress(3,4)
  const root = Poseidon.hash([n01, n23]); // compress(compress(1,2),compress(3,4))

  console.log('[1] cross-system root agreement (Rust dregg <-> o1js Mina)');
  console.log('    o1js root  = 0x' + root.toBigInt().toString(16).padStart(64, '0'));
  console.log('    rust root  = 0x' + RUST_GOLD_ROOT.toString(16).padStart(64, '0'));
  if (root.toBigInt() === RUST_GOLD_ROOT) {
    ok('o1js Poseidon Merkle root == Rust mina_poseidon_hash root (bit-for-bit)');
  } else {
    fail('o1js root diverged from the Rust dregg-side hasher');
    return;
  }

  // 2) Compile the Mina-side verifier.
  console.log('\n[2] compiling the Mina-side attestation circuit...');
  const t0 = Date.now();
  await DreggMembershipAttestation.compile();
  ok(`compiled in ${((Date.now() - t0) / 1000).toFixed(1)}s`);

  // 3) Prove membership of leaf value 3 (index 2) under the dregg root.
  //    index 2 = l2: level0 sibling=l3=4 (current is LEFT), level1 sibling=n01
  //    (current is RIGHT).
  const leaf = Field(3);
  const siblings = [Field(4), n01];
  const currentIsRight = [Bool(false), Bool(true)];

  console.log('\n[3] proving: leaf 3 is committed under the dregg root...');
  const t1 = Date.now();
  const { proof } = await DreggMembershipAttestation.proveMembership(
    root,
    leaf,
    siblings,
    currentIsRight,
  );
  ok(`proof produced in ${((Date.now() - t1) / 1000).toFixed(1)}s`);

  const verified = await DreggMembershipAttestation.verify(proof);
  if (verified) ok('Mina-side proof VERIFIES');
  else fail('proof failed to verify');

  if (proof.publicOutput.toBigInt() === 3n) {
    ok('proof-carrying public output == 3 (the opened leaf, bound to the root)');
  } else {
    fail('public output was not the opened leaf');
  }

  // 4) Non-vacuity: a tampered witness must NOT prove (soundness polarity).
  console.log('\n[4] soundness: a wrong sibling must FAIL to prove...');
  try {
    await DreggMembershipAttestation.proveMembership(
      root,
      leaf,
      [Field(999), n01], // wrong level-0 sibling
      currentIsRight,
    );
    fail('a tampered witness still produced a proof (UNSOUND)');
  } catch (e) {
    ok('tampered witness rejected at proving time (constraint unsatisfiable)');
  }

  console.log(
    '\n=== ' +
      (process.exitCode ? 'FAILED' : 'PASS') +
      ' === (a Mina zkApp verified, in-circuit, a dregg-emitted Poseidon commitment)\n',
  );
}

main().catch((e) => {
  console.error(e);
  process.exitCode = 1;
});
