import {
  ZkProgram,
  Field,
  Poseidon,
  Provable,
  Bool,
  PrivateKey,
  PublicKey,
  Signature,
  SmartContract,
  State,
  state,
  method,
  type DeployArgs,
} from 'o1js';

// ---------------------------------------------------------------------------
// DreggPoseidonAttestation — the tractable mutual-proof step (Mina verifies a
// dregg-side Poseidon-over-Pasta commitment IN-CIRCUIT).
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
// Mina proof genuinely attests that a leaf is committed under a Pasta root the
// dregg-side hasher produced.
//
// ⚑ WHAT THIS IS NOT. The root the gate exercises is a FIXED-LEAF TEST VECTOR
// emitted by `mina_poseidon_hash` (the dregg-side Rust hasher), not a
// commitment to live dregg cell state — nothing in dregg emits a Mina-Poseidon
// root over real state today. So this attests that the two proof systems agree
// on a COMMITMENT SCHEME, not that Mina has verified a dregg state root. It is
// proof-carrying end-to-end only once dregg's own proof binds the attested
// Pasta root (Route A in the design doc, §6.1). This note answers
// docs/AUDIT-IMPORTER-AND-DOCS.md §3.4 (F-B8).
// ---------------------------------------------------------------------------

/** Mina's account/application Merkle trees are fixed-depth; 32 mirrors o1js
 *  MerkleTree/MerkleMap defaults and the dregg cell tree (types.ts TREE_DEPTH). */
export const ATTEST_DEPTH = 32;

// ---------------------------------------------------------------------------
// Out-of-circuit twins of the in-circuit fold. These call the same
// `Poseidon.hash` the circuit calls, so a divergence between them and the
// circuit is a real disagreement, not a re-implementation gap.
// ---------------------------------------------------------------------------

/** The MMCS 2->1 node compression: Rust `compress(l, r)` == o1js
 *  `Poseidon.hash([l, r])` == one Mina-Poseidon permutation. */
export function compress(left: Field, right: Field): Field {
  return Poseidon.hash([left, right]);
}

/** A Merkle authentication path, bottom-up. `isRight[i]` says whether the
 *  CURRENT node is the right child at level `i` (so the sibling is on the left). */
export type MerklePath = { siblings: Field[]; isRight: Bool[] };

/**
 * Fold a leaf up a path, returning every intermediate node (index `i` is the
 * node after absorbing level `i`; the last entry is the root). The gate uses
 * the intermediates to pin the depth-2 subtree against the Rust probe's
 * committed vector.
 */
export function foldPath(leaf: Field, path: MerklePath): Field[] {
  const out: Field[] = [];
  let current = leaf;
  for (let i = 0; i < path.siblings.length; i++) {
    const right = path.isRight[i].toBoolean();
    current = right
      ? compress(path.siblings[i], current)
      : compress(current, path.siblings[i]);
    out.push(current);
  }
  return out;
}

/**
 * Build the depth-`depth` authentication path for `leafIndex` in a sparse tree
 * whose populated leaves are `leaves[0..n)` and whose remaining leaves are
 * `Field(0)`.
 */
export function sparsePath(
  leaves: Field[],
  leafIndex: number,
  depth: number,
): { path: MerklePath; nodes: Field[]; root: Field } {
  // `zeroAt[h]` is the node value of an all-zero subtree of height `h`.
  const zeroAt: Field[] = [Field(0)];
  for (let h = 1; h <= depth; h++)
    zeroAt.push(compress(zeroAt[h - 1], zeroAt[h - 1]));

  let level = leaves.slice();
  let index = leafIndex;
  const siblings: Field[] = [];
  const isRight: Bool[] = [];

  for (let h = 0; h < depth; h++) {
    const sibIndex = index ^ 1;
    siblings.push(sibIndex < level.length ? level[sibIndex] : zeroAt[h]);
    isRight.push(Bool(index % 2 === 1));
    const next: Field[] = [];
    for (let i = 0; i < level.length; i += 2) {
      const l = level[i];
      const r = i + 1 < level.length ? level[i + 1] : zeroAt[h];
      next.push(compress(l, r));
    }
    level = next;
    index = index >> 1;
  }

  const path = { siblings, isRight };
  const nodes = foldPath(leaves[leafIndex], path);
  return { path, nodes, root: nodes[nodes.length - 1] };
}

// ---------------------------------------------------------------------------
// The in-circuit verifier.
// ---------------------------------------------------------------------------

/**
 * Build a `DreggMembershipAttestation` ZkProgram at a given path depth.
 *
 *   publicInput  = the dregg-side Pasta root (Mina-Poseidon over Pasta Fp)
 *   publicOutput = the opened leaf (a proof-carrying attestation of its value)
 *
 * The depth is baked in because `Provable.Array` needs a static length, so this
 * is a factory rather than a single constant program.
 */
export function makeDreggMembershipAttestation(depth: number) {
  return ZkProgram({
    name: `dregg-membership-attestation-d${depth}`,
    publicInput: Field,
    publicOutput: Field,
    methods: {
      proveMembership: {
        privateInputs: [
          Field, //                        leaf (private witness)
          Provable.Array(Field, depth), // sibling hashes, bottom-up
          Provable.Array(Bool, depth), //  currentIsRightChild per level
        ],
        async method(
          dreggRoot: Field,
          leaf: Field,
          siblings: Field[],
          currentIsRight: Bool[],
        ) {
          let current = leaf;
          for (let i = 0; i < depth; i++) {
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
}

/** The canonical program, at the dregg cell-tree depth. */
export const DreggMembershipAttestation =
  makeDreggMembershipAttestation(ATTEST_DEPTH);

/** The proof type produced by the attestation program. */
export class DreggAttestationProof extends ZkProgram.Proof(
  DreggMembershipAttestation,
) {}

/**
 * DreggAttestedGate: a zkApp whose action is gated on a verified dregg
 * membership attestation. This is the proof-carrying composition — the zkApp
 * `.verify()`s the attestation and binds it to the root it tracks.
 *
 * `setDreggRoot` is the trusted-relay anchor (design doc §3/§6.1); the novel
 * part is `actOnAttestedLeaf`, which consumes a REAL recursive proof rather
 * than a bare structural assert.
 *
 * ⚑ WHY THE RELAY KEY IS IN STATE AND THE SIGNATURE IS CHECKED IN CIRCUIT.
 * An earlier shape of this contract had a bare `setDreggRoot(newRoot)` whose
 * comment said "relay-authorized" and whose body checked nothing. Under Mina's
 * DEFAULT permissions `editState` is `proof`, and a proof of an unconditional
 * method is something ANY caller can produce — so the anchor was open to
 * everyone while reading as a trust boundary. Mina's per-field permissions
 * cannot fix that on their own: `editState` governs BOTH methods of this
 * contract, so there is no permission that admits `actOnAttestedLeaf` and
 * restricts `setDreggRoot`. The authorization therefore has to be a condition
 * the CIRCUIT asserts, which is what `auth.verify(...).assertTrue()` below is.
 */
export class DreggAttestedGate extends SmartContract {
  /** The Pasta state root this gate trusts. This is `app_state_0` — the slot
   *  the daemon names in `Account_app_state_0_precondition_unsatisfied`, so its
   *  position is load-bearing for the deployment record and must stay first. */
  @state(Field) dreggRoot = State<Field>();
  /** The last leaf a proof successfully opened under `dreggRoot`. */
  @state(Field) lastAttestedLeaf = State<Field>();
  /** The relay authorized to re-anchor the root. A `PublicKey` occupies two
   *  field slots (x, isOdd), so this gate uses 4 of the 8 available. Written
   *  ONCE, by the deploy account update — which is signature-authorized, so
   *  only the holder of the zkApp key can install it — and no method changes
   *  it. A relay rotation is therefore a redeploy, which is the honest shape
   *  for a demo: rotation is a real design question, not a free method. */
  @state(PublicKey) relay = State<PublicKey>();

  /**
   * Deploying REQUIRES naming the relay. Without it the gate would ship with
   * `relay = PublicKey.empty()`, and `setDreggRoot` would be unusable rather
   * than open — but "unusable" is not a state anyone should discover on chain,
   * so this refuses at transaction-build time instead.
   */
  async deploy(props?: DeployArgs & { relay?: PublicKey }) {
    await super.deploy(props);
    const relay = props?.relay;
    if (relay === undefined || relay.isEmpty().toBoolean()) {
      throw new Error(
        'DreggAttestedGate.deploy({ relay }) requires a non-empty relay PublicKey: ' +
          'it is the only key that can ever re-anchor this gate.',
      );
    }
    this.relay.set(relay);
  }

  /**
   * Anchor a root. AUTHORIZED, and the authorization is checked here:
   * `auth` must be a Schnorr signature by the relay public key held in state,
   * over the exact transition `[oldRoot, newRoot]`. Failing that check makes
   * the constraint system unsatisfiable, so an unauthorized caller cannot
   * produce a transaction at all.
   *
   * Binding to `oldRoot` (rather than to `newRoot` alone) makes each
   * authorization specific to one state transition, and makes the transaction
   * carry an `app_state_0` precondition — so an authorization issued against a
   * root that has since advanced is refused by the network too.
   *
   * ⚑ The one thing this does NOT prevent: if the anchored root ever returned
   * to `oldRoot`, a captured `auth` for `oldRoot -> newRoot` would be valid
   * again. Roots here are fresh Poseidon images, so that is not reachable in
   * practice, but the contract does not itself forbid it. Saying so beats a
   * comment that implies a replay counter the code does not have.
   */
  @method async setDreggRoot(newRoot: Field, auth: Signature) {
    newRoot.assertNotEquals(Field(0));
    const relay = this.relay.getAndRequireEquals();
    const oldRoot = this.dreggRoot.getAndRequireEquals();
    auth
      .verify(relay, [oldRoot, newRoot])
      .assertTrue('setDreggRoot: not signed by the anchored relay key');
    this.dreggRoot.set(newRoot);
  }

  /**
   * Gate an action on a proof that a leaf is committed under the root this
   * zkApp tracks. The proof is a real recursive attestation; the zkApp checks
   * (a) it verifies and (b) it is bound to OUR root.
   */
  @method async actOnAttestedLeaf(proof: DreggAttestationProof) {
    proof.verify();
    const root = this.dreggRoot.getAndRequireEquals();
    // The proof's public input is the root it proved membership against.
    proof.publicInput.assertEquals(root);
    // The public output is the attested leaf; record it so the gate's effect is
    // observable on-chain (an unrecorded gate is an unobservable one).
    const leaf = proof.publicOutput;
    leaf.assertNotEquals(Field(0));
    this.lastAttestedLeaf.set(leaf);
  }
}

/**
 * The message `setDreggRoot` verifies, in ONE place. The signer and the
 * verifier reading the same function is what stops them drifting into a
 * signature that binds something other than what the circuit checks — the
 * failure this repo has hit before (a signed `effects_hash` compared against
 * nothing).
 */
export function anchorAuthMessage(oldRoot: Field, newRoot: Field): Field[] {
  return [oldRoot, newRoot];
}

/** Produce the relay authorization for `oldRoot -> newRoot`. */
export function signAnchor(
  relayKey: PrivateKey,
  oldRoot: Field,
  newRoot: Field,
): Signature {
  return Signature.create(relayKey, anchorAuthMessage(oldRoot, newRoot));
}
