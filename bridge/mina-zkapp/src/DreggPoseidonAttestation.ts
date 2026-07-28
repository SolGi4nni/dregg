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
import {
  BbDigest,
  foldOpening,
  sparsePathBigInt,
} from './Poseidon2Merkle.js';

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

// ---------------------------------------------------------------------------
// THE ANCHOR OBLIGATION — a PROOF, and an honest account of what it is not.
//
// ⚑ READ THIS BEFORE READING `setDreggRoot`.
//
// dregg's thesis is proof-as-capability. `chain/contracts/DreggPeerRegistry.sol`
// accepts a peer root because a FINALITY PROOF VERIFIED — no owner, no
// committee. The Mina side does not have that yet, and the reason is measured,
// not vague: verifying dregg's root FRI-STARK inside Kimchi costs ~2.9e7 rows,
// several hundred chained Pickles steps (docs/MINA-VERIFIES-DREGG-FRI-SIZE.md),
// of which ONE FRI query alone is 684,726 measured rows — 13–15 steps.
//
// An earlier lane closed a real hole (a `setDreggRoot` with no authorization at
// all) with an IN-CIRCUIT SCHNORR SIGNATURE BY A RELAY KEY HELD IN STATE. That
// fixed the hole and got the architecture backwards: an anchor accepted because
// ONE KEY SIGNED IT is an oracle bridge wearing a zkApp.
//
// What this contract does now, stated so nobody has to infer it:
//
//   1. `setDreggRoot` takes a PROOF, and the anchored root is that proof's
//      PUBLIC INPUT — there is no way to anchor a value the proof does not
//      claim. The statement is `DreggAnchorStatement` below.
//   2. The relay signature is STILL THERE and is STILL what makes the anchor
//      unforgeable. It is named `placeholderAuth`, it is not called
//      authorization anywhere, and it is scheduled for deletion by the FRI
//      verifier, not by a redesign of the signature.
//
// Deleting the key today would make the anchor world-writable, because the
// obligation in (1) is a SHAPE constraint, not a claim about dregg's state. So
// the key stays and is labelled. It is a stopgap. It is not the fix.
// ---------------------------------------------------------------------------

/**
 * The tree height `DreggAnchorStatement` opens under.
 *
 * ⚑ ARBITRARY, and that is worth saying rather than burying: nothing in dregg
 * emits a BabyBear-Poseidon2 commitment over live cell state today, so there is
 * no deployed tree height to match. What the statement constrains is that the
 * anchored value is the Mina-side image of a REAL MMCS root — the height is a
 * cost knob. The deployed FRI input phase is depth 22
 * (`DEPLOYED_INPUT_PHASE_DEPTH`), measured at 58,971 rows; this is smaller so
 * the gate compiles in seconds rather than minutes.
 */
export const ANCHOR_MERKLE_DEPTH = 4;

/**
 * **The obligation `setDreggRoot` discharges.**
 *
 *   publicInput  = the Pasta root being anchored (`app_state_0`)
 *   publicOutput = the VOUCH: the Mina-side image of the BabyBear MMCS root
 *
 * Two folds, in two different hashes, joined at a leaf:
 *
 *   1. Open a leaf under the DEPLOYED BabyBear Poseidon2-w16 MMCS
 *      (`TruncatedPermutation<Perm, 2, 8, 16>` — the same compression
 *      `circuit-prove/src/plonky3_recursion_impl.rs:128` instantiates) to a
 *      root `R_bb`. This is Rung 1, in the anchor.
 *   2. Set `vouch = Poseidon(R_bb)` — one Pasta field element — and fold it up
 *      `ATTEST_DEPTH` levels of Mina-Poseidon as **leaf 0** of the anchored
 *      tree. Leaf 0 means every level is a LEFT child, so there is no direction
 *      to witness and no slot for the prover to choose: the vouch's POSITION is
 *      structural, not asserted.
 *
 * The anchored root is therefore a Pasta tree — which is what
 * `actOnAttestedLeaf` opens against, so the two compose — whose slot 0 commits
 * to a BabyBear-Poseidon2 MMCS root the prover exhibited an opening of.
 *
 * ⚑ WHAT THIS PROVES. The anchored value is not an arbitrary field element: it
 * is a Mina-Poseidon Merkle root whose designated slot holds `Poseidon(R_bb)`
 * for an `R_bb` the prover built and can open. Poseidon preimage resistance
 * forbids working backwards from a chosen anchor, so this is not vacuous.
 *
 * ⚑ WHAT THIS DOES NOT PROVE, and it IS the whole distance to a real gate:
 * that `R_bb` is dregg's state root; that any dregg turn executed; that any
 * dregg proof verified; that this root follows the previous one by a legal
 * transition. **Anyone can build a Merkle tree.** This narrows the anchor from
 * "any field element" to "a commitment with a known opening". It does not
 * authorize. The thing that authorizes is still `placeholderAuth` — a key.
 */
export const DreggAnchorStatement = ZkProgram({
  name: 'dregg-anchor-statement',
  publicInput: Field,
  publicOutput: Field,
  methods: {
    proveAnchorShape: {
      privateInputs: [
        BbDigest, //                                        the opened BabyBear leaf digest
        Provable.Array(BbDigest, ANCHOR_MERKLE_DEPTH), //   BabyBear siblings, bottom-up
        Provable.Array(Bool, ANCHOR_MERKLE_DEPTH), //       BabyBear path directions
        Provable.Array(Field, ATTEST_DEPTH), //             Pasta siblings for slot 0
      ],
      async method(
        anchored: Field,
        leaf: BbDigest,
        bbSiblings: BbDigest[],
        bbIsRight: Bool[],
        pastaSiblings: Field[],
      ) {
        const bbRoot = foldOpening(leaf, bbSiblings, bbIsRight);
        const vouch = Poseidon.hash(bbRoot.limbs);
        // Leaf 0 of the anchored tree: LEFT child at every level, so the
        // position is fixed by the shape of the circuit and not witnessed.
        let cur = vouch;
        for (let i = 0; i < ATTEST_DEPTH; i++) cur = Poseidon.hash([cur, pastaSiblings[i]]);
        cur.assertEquals(anchored);
        return { publicOutput: vouch };
      },
    },
  },
});

/** The leaf index of the BabyBear vouch in the anchored Pasta tree. Structural:
 *  the circuit folds LEFT at every level, so this is 0 and cannot be moved
 *  without changing the circuit. */
export const ANCHOR_VOUCH_INDEX = 0;

/** The proof type `setDreggRoot` consumes. */
export class DreggAnchorProof extends ZkProgram.Proof(DreggAnchorStatement) {}

/** The VOUCH: the Mina-side image of a BabyBear MMCS root. Exposed so a caller
 *  and the circuit compute it in ONE place — the drift this repo has paid for
 *  before is two sides computing "the same" message differently. */
export function vouchOfBbRoot(bbRoot: bigint[] | Field[]): Field {
  return Poseidon.hash(bbRoot.map((x) => (typeof x === 'bigint' ? Field(x) : x)));
}

/**
 * DreggAttestedGate: a zkApp whose action is gated on a verified dregg
 * membership attestation, and whose anchored root is gated on a verified
 * `DreggAnchorStatement` proof.
 *
 * ⚑ WHY THE PLACEHOLDER KEY IS STILL IN STATE AND STILL CHECKED IN CIRCUIT.
 * Under Mina's DEFAULT permissions `editState` is `proof`, and a proof of an
 * unconditional method is something ANY caller can produce — so an anchor whose
 * only gate is "some proof verified" is open to everyone unless the CIRCUIT
 * narrows who. Mina's per-field permissions cannot help: `editState` governs
 * every method of this contract at once. Until the anchor's obligation is
 * strong enough to stand alone (i.e. until it is the FRI verify), removing the
 * key removes the only thing that makes the anchor unforgeable. It stays,
 * labelled, and the docs say what it is.
 *
 * ⚑ AND "UNTIL IT IS THE FRI VERIFY" IS NOW A MEASURED DISTANCE, NOT A GESTURE.
 * `docs/MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.9-3.16 prices the ladder against the
 * deployed p3 objects. As of 2026-07-28 the FRI query indices and fold
 * challenges are DERIVED from a Fiat-Shamir transcript (§3.12, 62,637 rows)
 * rather than witnessed, one program joins the derivation to a whole 16-layer
 * commit phase (§3.13b), and — the item that used to be second on this list —
 * the reduced opening the chain starts from is now the DEEP QUOTIENT of the
 * MMCS-opened rows rather than a witness (§3.15, 154,523 rows/query). So the
 * walk is over the PROVER's queries AND it is about the PROVER's trace.
 *
 * ⚑ THAT SECOND ITEM DID NOT CLOSE BY ASSERTION. `makeDeepBoundQueryProgram`
 * keeps the pre-§3.15 statement compiled beside the new one, and the gate PROVES
 * a witness the old statement admits and requires the new one to REFUSE the same
 * public claim. Every run.
 *
 * FIVE things still stand between that and an anchor this key could be deleted
 * from, and §3.14 keeps the list:
 *
 *   1. the transcript's preamble is a stand-in, not the batch-STARK's own
 *      observes — and §3.16 measures what the real one costs: 2.97e6 rows of
 *      challenger permutations just to absorb the 2,286 opened values, against
 *      the 13 lanes §3.12 stands in with;
 *   2. the AIR constraint evaluation at zeta is STARTED but not finished
 *      (§3.16): the selectors, the alpha-fold, the quotient-chunk recomposition
 *      and the closing equality are built and KAT'd against p3's own domain
 *      algebra, but `C_i` — dregg's seven AIRs — is not, and its constraint
 *      count N is uncounted. Until it is, the walk authenticates a low-degree
 *      function that encodes nothing in particular;
 *   3. the input-phase MMCS opening carries ONE matrix per batch;
 *      `verify_batch` over several matrices of MIXED heights is priced and not
 *      implemented;
 *   4. every rung walks ONE query of nineteen;
 *   5. the root's own `degree_bits` has never been read (§1.3), and the roll-in
 *      schedule is a function of it (§3.15d).
 *
 * None of those is a reason to delete the key early. All five closing is.
 */
export class DreggAttestedGate extends SmartContract {
  /** The Pasta state root this gate trusts. This is `app_state_0` — the slot
   *  the daemon names in `Account_app_state_0_precondition_unsatisfied`, so its
   *  position is load-bearing for the deployment record and must stay first. */
  @state(Field) dreggRoot = State<Field>();
  /** The last leaf a proof successfully opened under `dreggRoot`. */
  @state(Field) lastAttestedLeaf = State<Field>();
  /** ⚑ A PLACEHOLDER, NOT AN AUTHORIZATION DESIGN. The key whose signature
   *  `setDreggRoot` currently also requires, because the anchor's PROOF
   *  obligation is a shape constraint and cannot yet stand alone. A `PublicKey`
   *  occupies two field slots (x, isOdd), so this gate uses 4 of the 8
   *  available. Written ONCE, by the deploy account update — which is
   *  signature-authorized, so only the holder of the zkApp key can install it —
   *  and no method changes it. It is deleted when `DreggAnchorStatement`
   *  becomes the FRI verify, not before. */
  @state(PublicKey) placeholderRelay = State<PublicKey>();

  /**
   * Deploying REQUIRES naming the placeholder relay. Without it the gate would
   * ship with `placeholderRelay = PublicKey.empty()`, and `setDreggRoot` would
   * be unusable rather than open — but "unusable" is not a state anyone should
   * discover on chain, so this refuses at transaction-build time instead.
   */
  async deploy(props?: DeployArgs & { placeholderRelay?: PublicKey }) {
    await super.deploy(props);
    const relay = props?.placeholderRelay;
    if (relay === undefined || relay.isEmpty().toBoolean()) {
      throw new Error(
        'DreggAttestedGate.deploy({ placeholderRelay }) requires a non-empty PublicKey: ' +
          'it is the STOPGAP that currently keeps the anchor from being world-writable.',
      );
    }
    this.placeholderRelay.set(relay);
  }

  /**
   * Anchor a root.
   *
   * TWO conditions, and they are not the same kind of thing:
   *
   *   (a) A PROOF OBLIGATION. `anchor` must be a verifying proof of
   *       `DreggAnchorStatement`, and the anchored root IS its public input —
   *       so no value can be anchored that the proof does not claim. Read that
   *       statement's doc for exactly what it establishes (the anchored value
   *       is the Mina image of a real BabyBear-Poseidon2 MMCS root) and exactly
   *       what it does not (anything at all about dregg's state).
   *
   *   (b) A PLACEHOLDER SIGNATURE. `placeholderAuth` must be a Schnorr
   *       signature by `placeholderRelay` over `[oldRoot, newRoot]`. ⚑ This is
   *       the trusted part, and it is the ONLY thing that currently makes the
   *       anchor unforgeable. It is a stopgap for the FRI verify, not a design.
   *
   * Binding (b) to `oldRoot` makes each signature specific to one transition,
   * and makes the transaction carry an `app_state_0` precondition — so a
   * signature issued against a root that has since advanced is refused by the
   * network too.
   *
   * ⚑ The one thing (b) does NOT prevent: if the anchored root ever returned to
   * `oldRoot`, a captured signature for `oldRoot -> newRoot` would be valid
   * again. Roots here are fresh Poseidon images, so that is not reachable in
   * practice, but the contract does not itself forbid it. Saying so beats a
   * comment that implies a replay counter the code does not have.
   */
  @method async setDreggRoot(anchor: DreggAnchorProof, placeholderAuth: Signature) {
    // (a) the obligation.
    anchor.verify();
    const newRoot = anchor.publicInput;
    newRoot.assertNotEquals(Field(0));

    const oldRoot = this.dreggRoot.getAndRequireEquals();

    // (b) the placeholder. NOT the authorization design — see the header.
    const relay = this.placeholderRelay.getAndRequireEquals();
    placeholderAuth
      .verify(relay, placeholderAuthMessage(oldRoot, newRoot))
      .assertTrue('setDreggRoot: not signed by the PLACEHOLDER relay key');

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
 * The message the PLACEHOLDER signature covers, in ONE place. The signer and
 * the verifier reading the same function is what stops them drifting into a
 * signature that binds something other than what the circuit checks — the
 * failure this repo has hit before (a signed `effects_hash` compared against
 * nothing).
 */
export function placeholderAuthMessage(oldRoot: Field, newRoot: Field): Field[] {
  return [oldRoot, newRoot];
}

/** Produce the PLACEHOLDER signature for `oldRoot -> newRoot`. Named for what
 *  it is: this is not an authorization primitive, it is the stopgap standing in
 *  for a FRI verify that does not fit yet. */
export function signPlaceholderAnchor(
  relayKey: PrivateKey,
  oldRoot: Field,
  newRoot: Field,
): Signature {
  return Signature.create(relayKey, placeholderAuthMessage(oldRoot, newRoot));
}

/**
 * Everything a caller needs to anchor: build a fresh BabyBear MMCS tree, derive
 * the vouch, place it at slot 0 of a Pasta tree whose other leaves are
 * `otherPastaLeaves`, and prove `DreggAnchorStatement`.
 *
 * The anchored root and the proof come out of ONE function so they cannot
 * disagree — a caller that computed the root itself and proved separately is
 * the shape that lets a proof bind something other than what is written.
 *
 * `DreggAnchorStatement.compile()` must have run first.
 */
export async function proveAnchor(
  bbLeaves: bigint[][],
  bbLeafIndex: number,
  otherPastaLeaves: Field[],
): Promise<{
  proof: DreggAnchorProof;
  anchoredRoot: Field;
  vouch: Field;
  bbRoot: bigint[];
  pastaLeaves: Field[];
}> {
  const bb = sparsePathBigInt(bbLeaves, bbLeafIndex, ANCHOR_MERKLE_DEPTH);
  const vouch = vouchOfBbRoot(bb.root);
  const pastaLeaves = [vouch, ...otherPastaLeaves];
  const pasta = sparsePath(pastaLeaves, ANCHOR_VOUCH_INDEX, ATTEST_DEPTH);
  const anchoredRoot = pasta.root;
  const { proof } = await DreggAnchorStatement.proveAnchorShape(
    anchoredRoot,
    BbDigest.from(bbLeaves[bbLeafIndex]),
    bb.siblings.map((s) => BbDigest.from(s)),
    bb.isRight.map((b) => Bool(b)),
    pasta.path.siblings,
  );
  return { proof, anchoredRoot, vouch, bbRoot: bb.root, pastaLeaves };
}

/** A tree of BabyBear leaf digests derived from `seed` — for callers that need
 *  a fresh anchorable commitment and have no live dregg state to commit to
 *  (which is every caller today; see `DreggAnchorStatement`'s doc). */
export function anchorLeavesFromSeed(seed: bigint, n = 4): bigint[][] {
  const P_BB = 2013265921n;
  return Array.from({ length: n }, (_, i) =>
    Array.from({ length: 8 }, (_, j) => ((seed + 1n) * BigInt(i * 31 + j + 1) + BigInt(j)) % P_BB),
  );
}
