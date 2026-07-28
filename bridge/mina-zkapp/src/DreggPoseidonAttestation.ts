import {
  ZkProgram,
  Field,
  Poseidon,
  Provable,
  Bool,
  SmartContract,
  State,
  state,
  method,
} from 'o1js';

// ---------------------------------------------------------------------------
// DreggPoseidonAttestation — the tractable mutual-proof step (Mina verifies a
// dregg-emitted Poseidon-over-Pasta commitment IN-CIRCUIT).
//
// Verifying dregg's REAL proof (a gnark Groth16 on BN254) inside a Mina/Kimchi
// (Pasta/IPA) zkApp is infeasible today: Kimchi has no pairing gate and
// emulating one exceeds the 2^16-row step ceiling (docs/MINA-DREGG-ZKAPP-BRIDGE.md).
// The tractable step uses the ONE primitive both systems compute bit-for-bit:
// Mina-Poseidon over Pasta Fp (o1js `Poseidon.hash` == Rust `mina_poseidon_hash`,
// gold-KAT-pinned by circuit-prove/sketches/mina-pasta-hash-probe).
//
// This wires in the real Poseidon Merkle fold that types.ts ships as
// `CellMerkleWitness.computeRoot` but never put inside a provable method — so a
// Mina proof genuinely attests that a leaf is committed under a dregg root.
//
// Boundary: this attests dregg's COMMITMENT, not dregg's PROOF. It is
// proof-carrying end-to-end only once dregg's proof binds the attested Pasta
// root (Route A in the design doc). See §6.1 there.
// ---------------------------------------------------------------------------

/** Mina's account/application Merkle trees are fixed-depth; 32 mirrors o1js
 *  MerkleTree/MerkleMap defaults and the dregg cell tree (types.ts TREE_DEPTH). */
export const ATTEST_DEPTH = 32;

/**
 * DreggMembershipAttestation: an o1js recursive proof that a leaf is committed
 * under a dregg-emitted Pasta state root, via a native Poseidon Merkle path.
 *
 *   publicInput  = the dregg-emitted Pasta root (Mina-Poseidon over Pasta Fp)
 *   publicOutput = the opened leaf (a proof-carrying attestation of its value)
 */
export const DreggMembershipAttestation = ZkProgram({
  name: 'dregg-membership-attestation',
  publicInput: Field,
  publicOutput: Field,
  methods: {
    proveMembership: {
      privateInputs: [
        Field, //                              leaf (private witness)
        Provable.Array(Field, ATTEST_DEPTH), // sibling hashes, bottom-up
        Provable.Array(Bool, ATTEST_DEPTH), //  currentIsRightChild per level
      ],
      async method(
        dreggRoot: Field,
        leaf: Field,
        siblings: Field[],
        currentIsRight: Bool[],
      ) {
        let current = leaf;
        for (let i = 0; i < ATTEST_DEPTH; i++) {
          // If `current` is the right child, the sibling is on the left.
          const left = Provable.if(currentIsRight[i], siblings[i], current);
          const right = Provable.if(currentIsRight[i], current, siblings[i]);
          current = Poseidon.hash([left, right]); // == Rust compress(l, r)
        }
        current.assertEquals(dreggRoot);
        return { publicOutput: leaf };
      },
    },
  },
});

/** The proof type produced by the attestation program. */
export class DreggAttestationProof extends ZkProgram.Proof(
  DreggMembershipAttestation,
) {}

/**
 * DreggAttestedGate: a zkApp whose action is gated on a verified dregg
 * membership attestation. This is the proof-carrying composition — the zkApp
 * `.verify()`s the attestation and binds it to the dregg root it tracks.
 *
 * `advanceRoot` here stands in for the trusted-relay anchor (see the design
 * doc §3/§6.1); the novel part is `actOnAttestedLeaf`, which consumes a REAL
 * recursive proof rather than a bare structural assert.
 */
export class DreggAttestedGate extends SmartContract {
  /** The dregg-emitted Pasta state root this gate trusts. */
  @state(Field) dreggRoot = State<Field>();

  /** Anchor the dregg root (relay-authorized; the trust boundary, §3). */
  @method async setDreggRoot(newRoot: Field) {
    newRoot.assertNotEquals(Field(0));
    this.dreggRoot.set(newRoot);
  }

  /**
   * Gate an action on a proof that `attestedLeaf` is committed under the
   * dregg root this zkApp tracks. The proof is a real recursive attestation;
   * the zkApp checks (a) it verifies and (b) it is bound to OUR root.
   */
  @method async actOnAttestedLeaf(proof: DreggAttestationProof) {
    proof.verify();
    const root = this.dreggRoot.getAndRequireEquals();
    // The proof's public input is the root it proved membership against.
    proof.publicInput.assertEquals(root);
    // proof.publicOutput is the attested leaf, now usable by downstream logic
    // (mint, capability grant, membership receipt, ...).
    proof.publicOutput.assertNotEquals(Field(0));
  }
}
