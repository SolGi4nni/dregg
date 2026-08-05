// DREGG CAPABILITY GATE — a Mina zkApp whose state advances only when someone EXERCISES a dregg
// capability that chains to an authority the gate holds, within a narrowing the gate never saw.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ THE ONE CLAIM
//
// This contract honors a capability exercise proved under a verification key IT HAS NEVER SEEN and
// CANNOT NAME, because the key that DID verify the parent vouched for the child — and it enforces,
// in-circuit, that the child's scope is a narrowing of the parent's under dregg's own facet lattice
// (`cell/src/facet.rs`). That is dregg's attenuation clause, running on Mina.
//
// ⚑ AND THE RESOLUTION IT HOLDS AT. What gets verified is a proof of the ATTENUATION ALGEBRA — that
// a chain of capability programs narrowed monotonically from a named root, and that the requested
// effect and amount fall inside the narrowest scope. It is NOT a proof of the dregg TURN. The dregg
// STARK cannot be side-loaded here today; `exerciseTurn`'s `witnessTurn*` arguments are the exact
// line where that proof plugs in, and they are marked COMMITTED-NOT-VERIFIED there, in the code, at
// the assertion that does not exist. See that comment for what is missing and why.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ WHAT THE GATE TRUSTS, AND WHAT IT DERIVES
//
// TRUSTED — TWO key hashes and a subject, on-chain state, set once at deploy:
//   • `rootAuthority`     — which capability TREE. The root program's verification-key hash.
//   • `attenuatorProgram` — which narrowing RULE. `DreggAttenuate`'s verification-key hash.
//   • `subjectHi/Lo`      — the dregg `CellId` this gate's capabilities are over.
//
// ⚑ THE SECOND ONE IS NOT OPTIONAL AND AN EARLIER REVISION OF THIS FILE OMITTED IT. `authority` is
// unforgeable, so pinning the root alone proves the chain really descends from it — but not that the
// descent NARROWED, because the program that computed the child's scope is the prover's choice.
// `DreggRogueAttenuate` (DreggCapability.ts) is exactly that program: honest ancestry, no narrowing
// check, arbitrary output scope. Read its doc for why fixing the rule is correct rather than a
// retreat — the DELEGATES stay unbounded and unseen; only the attenuation semantics is fixed, as it
// is in every capability system.
//
// DERIVED (every exercise, in-circuit, from the proof and the key the exerciser brought):
//   • that the presented key really verified the presented proof            (Pickles, side-loaded)
//   • that the key's hash matches the key's bytes           (o1js, zkprogram.js:557-563)
//   • that the chain of narrowings terminates at `rootAuthority`   (`DreggAttenuate`, this file)
//   • that the requested effect is permitted by the narrowed mask          (facet.rs:160-166)
//   • that the requested amount is under the narrowed ceiling              (facet.rs:355-361)
//
// NOT DERIVED, and named so in the code rather than in a note: that the dregg turn named in the
// receipt happened.
//
// ═════════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ REVOCATION IS THE ASYMMETRY, AND IT IS REAL
//
// dregg has `Effect::RevokeCapability` (`turn/src/action.rs:1056`, verb-registry `.survivor .revoke`
// at `Dregg2/Substrate/VerbRegistry.lean:296`). This gate has NO revocation of an individual
// delegate, and cannot have one without a nullifier set or a delegate registry: it never learns a
// delegate's key until the delegate turns up, so there is nothing to put on a list in advance.
// `rotateAuthority` revokes EVERY outstanding delegation at once by moving the root — a blunt
// instrument, and the honest description of what a bare vk-hash policy can express. A per-delegate
// revocation would need the gate to hold a Merkle root of revoked `authority`/key hashes and the
// exerciser to prove non-membership; that is a different contract, not a missing line in this one.

import {
  Field,
  Poseidon,
  SmartContract,
  State,
  UInt64,
  VerificationKey,
  method,
  state,
  type DeployArgs,
} from 'o1js';

import {
  DreggCapability,
  DreggDelegatedCapabilityProof,
  DreggRootCapabilityProof,
  isEffectPermittedInCircuit,
} from './DreggCapability.js';

/** Deploy-time settings. All three are required: a gate deployed without them would accept nothing
 *  (root `0` matches no real key hash), and "accepts nothing" is not a state to discover on chain. */
export type DreggCapabilityGateDeploy = DeployArgs & {
  /** Verification-key hash of the root capability program — which capability TREE. */
  rootAuthority?: Field;
  /** Verification-key hash of `DreggAttenuate` — which narrowing RULE. See the header: omitting
   *  this is the forgery `DreggRogueAttenuate` demonstrates. */
  attenuatorProgram?: Field;
  /** The dregg `CellId` these capabilities are over, split 16/16 bytes. */
  subjectHi?: Field;
  subjectLo?: Field;
};

export class DreggCapabilityGate extends SmartContract {
  /** ⚑ THE ONLY TRUSTED KEY. Everything else the gate honors is reached from here by attenuation.
   *  It is a hash, not key material: the gate never stores or needs the root's 1796 bytes, because
   *  the party that brings a proof brings the bytes (`Pickles.sideLoaded.inProver` takes the base64
   *  data, zkprogram.js:557). Holding only the hash is what makes the gate small. */
  @state(Field) rootAuthority = State<Field>();

  /** ⚑ THE NARROWING RULE. `DreggAttenuate`'s verification-key hash. This is what makes the mask on
   *  a delegated capability mean anything: without it the gate would accept a scope computed by any
   *  program at all, including one that skips the subset check. See the header and
   *  `DreggRogueAttenuate`. */
  @state(Field) attenuatorProgram = State<Field>();

  /** The dregg cell these capabilities are over. Carried unchanged through every attenuation step,
   *  so a delegate cannot re-point a narrowed capability at a different cell. */
  @state(Field) subjectHi = State<Field>();
  @state(Field) subjectLo = State<Field>();

  /** ⚑ THE RECEIPT. dregg's third clause. A running Poseidon chain over every exercise this gate
   *  honored — authority, subject, the narrowed mask, the effect exercised, the amount, and the
   *  dregg turn named. Chained rather than overwritten so the state is a history and not a
   *  last-write; an observer who has the sequence of exercises can recompute it and an observer who
   *  does not cannot forge one. */
  @state(Field) receiptChain = State<Field>();

  /** How many exercises have been honored. Redundant with the chain by construction, and kept
   *  because a chain value alone gives a reader no way to know how many folds produced it. */
  @state(Field) turnsHonored = State<Field>();

  async deploy(props?: DreggCapabilityGateDeploy) {
    await super.deploy(props);
    const root = props?.rootAuthority;
    const att = props?.attenuatorProgram;
    const hi = props?.subjectHi;
    const lo = props?.subjectLo;
    if (root === undefined || root.equals(0).toBoolean()) {
      throw new Error(
        'DreggCapabilityGate.deploy({ rootAuthority }) requires the root capability program\'s ' +
          'verification-key hash. `Field(0)` is the ROOT SENTINEL inside DreggCapability and would ' +
          'make the gate accept an unattenuated root claim from anyone.',
      );
    }
    if (att === undefined || att.equals(0).toBoolean()) {
      throw new Error(
        'DreggCapabilityGate.deploy({ attenuatorProgram }) requires DreggAttenuate\'s ' +
          'verification-key hash. Without it every delegated capability\'s scope is whatever the ' +
          'program that produced it chose to write — see DreggRogueAttenuate.',
      );
    }
    if (hi === undefined || lo === undefined) {
      throw new Error(
        'DreggCapabilityGate.deploy({ subjectHi, subjectLo }) requires the dregg CellId this gate ' +
          'is over; without it the gate would honor a capability over any cell.',
      );
    }
    this.rootAuthority.set(root);
    this.attenuatorProgram.set(att);
    this.subjectHi.set(hi);
    this.subjectLo.set(lo);
    this.receiptChain.set(Field(0));
    this.turnsHonored.set(Field(0));
  }

  /**
   * EXERCISE A DELEGATED CAPABILITY — the method the whole design exists for.
   *
   * ⚑ THE KEY IS THE EXERCISER'S. The gate does not know it, does not store it, and has never seen
   * it. o1js constrains `vk.hash` against `vk.data` while verifying (zkprogram.js:557-563), so it is
   * an identity and not a label, and `DreggAttenuate` set the capability's `authority` to exactly
   * that identity for the PARENT — which is what lets the gate accept a stranger's key.
   *
   * ⚑ ARITY-1 SLOT, AND THAT COVERS EVERY DEPTH. Attenuation is arity-preserving, so a delegate at
   * depth 1 and a delegate at depth 7 both come through here. See DreggCapability.ts's header for
   * why the arity is pinned at all — it is measured, not stylistic.
   *
   * @param effectBit  which of dregg's 28 effect bits is being exercised (cell/src/facet.rs:36-113)
   * @param amount     the transfer amount, checked against the narrowed `MaxTransferAmount`
   * @param witnessTurnHi/Lo  the dregg turn hash this exercise names, 16 bytes each
   */
  @method async exerciseDelegated(
    proof: DreggDelegatedCapabilityProof,
    vk: VerificationKey,
    effectBit: Field,
    amount: UInt64,
    witnessTurnHi: Field,
    witnessTurnLo: Field,
  ) {
    proof.verify(vk);
    const cap: DreggCapability = proof.publicOutput;

    // ── 1a. WHICH TREE. `authority` is `parentVk.hash`, pinned in-circuit to the bytes that
    // verified the parent, so this says: somebody really held a proof under the root's key. The gate
    // learns nothing about who, or how many narrowings happened, and does not need to.
    cap.authority.assertEquals(
      this.rootAuthority.getAndRequireEquals(),
      'delegated capability does not chain to this gate\'s root authority',
    );

    // ── 1b. ⚑ WHICH RULE. Descending from the root is not the same as having NARROWED, because the
    // program that wrote this capability's mask and ceiling was the prover's choice.
    // `DreggRogueAttenuate` satisfies 1a exactly and writes any scope it likes. This is the line
    // that refuses it, and without it the facet check below is checking a number the attacker
    // supplied.
    vk.hash.assertEquals(
      this.attenuatorProgram.getAndRequireEquals(),
      'delegated capability was not produced by the narrowing rule this gate holds',
    );

    this.checkAndRecord(cap, effectBit, amount, witnessTurnHi, witnessTurnLo);
  }

  /**
   * EXERCISE THE ROOT CAPABILITY DIRECTLY — arity 0, hence a second method and a second side-loaded
   * slot. See DreggCapability.ts's header: one slot admits exactly one arity, measured.
   *
   * ⚑ TWO CONJUNCTS AND BOTH ARE LOAD-BEARING. `cap.authority == 0` is the root sentinel, which any
   * root-shaped program emits and which therefore proves nothing on its own; `vk.hash == root` is
   * the identity of the key that just verified this proof. Dropping the second would let any program
   * that outputs `authority: 0` speak as the root, which is the whole vulnerability.
   */
  @method async exerciseDirect(
    proof: DreggRootCapabilityProof,
    vk: VerificationKey,
    effectBit: Field,
    amount: UInt64,
    witnessTurnHi: Field,
    witnessTurnLo: Field,
  ) {
    proof.verify(vk);
    const cap: DreggCapability = proof.publicOutput;

    const root = this.rootAuthority.getAndRequireEquals();
    cap.authority.assertEquals(Field(0), 'not a root capability (authority sentinel is not 0)');
    vk.hash.assertEquals(root, 'root capability presented under a key this gate does not hold');

    this.checkAndRecord(cap, effectBit, amount, witnessTurnHi, witnessTurnLo);
  }

  /**
   * Everything the two exercises share: subject, facet, budget, receipt. Not a `@method` — a plain
   * helper that emits constraints into whichever method called it, so the two paths cannot drift
   * apart in what they enforce.
   */
  private checkAndRecord(
    cap: DreggCapability,
    effectBit: Field,
    amount: UInt64,
    witnessTurnHi: Field,
    witnessTurnLo: Field,
  ) {
    // ── 2. SUBJECT. `DreggAttenuate` copies these through unchanged, so a delegate holding a
    // narrowed capability over cell A cannot present it against cell B.
    cap.subjectHi.assertEquals(this.subjectHi.getAndRequireEquals(), 'capability names another cell');
    cap.subjectLo.assertEquals(this.subjectLo.getAndRequireEquals(), 'capability names another cell');

    // ── 3. FACET. `is_effect_permitted(Some(mask), effectBit)` verbatim, INCLUDING the P2-1
    // `Some(0) = deny all` rule (cell/src/facet.rs:154-166). This is the assertion the narrowing
    // bites at: a delegate whose mask dropped a bit cannot exercise that bit, even though the ROOT
    // could and even though the same proof passes step 1.
    isEffectPermittedInCircuit(cap.effectMask, effectBit).assertTrue(
      'effect not permitted by the capability\'s facet mask (cell/src/facet.rs:160)',
    );

    // ── 4. BUDGET. `FacetConstraint::MaxTransferAmount` (cell/src/facet.rs:355-361). The ceiling is
    // whatever the LAST narrowing left, and `DreggAttenuate` refused to raise it.
    amount.assertLessThanOrEqual(
      UInt64.Unsafe.fromField(cap.maxTransfer),
      'transfer amount exceeds the capability\'s MaxTransferAmount (cell/src/facet.rs:355)',
    );

    // ── 5. RECEIPT.
    //
    // ⚑ COMMITTED, NOT VERIFIED — and this is the line the dregg proof plugs into.
    //
    // `witnessTurnHi/Lo` are folded into the receipt chain, so the gate's state records WHICH dregg
    // turn each honored exercise named, and an observer can recompute the chain. That is a
    // commitment. It is NOT a verification: no constraint above or below relates these two fields to
    // anything, so the exerciser chose them. The gate says "a holder of a capability narrowed from
    // my root, scoped to this effect and this ceiling, asserted turn T" — not "turn T happened".
    //
    // What closes it is one more `verify` here, of a dregg turn proof whose statement contains
    // `witnessTurnHi/Lo`. Two things stand in the way, and they are on different sides:
    //
    //   DREGG SIDE (checked at source 2026-08-05, GOAL-MINA-SEMANTIC-LIGHTCLIENTS.md third pass —
    //   ⚠ do NOT cite the older "22 vs 40 words" framing, it closed today). The wrap emission IS
    //   forty words in Pickles' own slot order and `kimchi::verifier::verify` ACCEPTS it under an
    //   index Mina builds from the key's own bytes, nothing padded. What is still missing is that
    //   the exposed values are that assembly's transcript over FIXTURE commitments rather than what
    //   `prepared_statement` derives from a real statement — so it is "not a Pickles-valid statement
    //   and not a Mina-valid proof", and the Pickles layer's own blockers (`expand_deferred`,
    //   `accumulator_check`) are untouched by the width fix. Side-loading is a PICKLES-layer
    //   verifier, so a kimchi-layer acceptance does not reach it.
    //
    //   THIS SIDE. `Pickles.sideLoaded.create` freezes `|publicInput|`, `|publicOutput|`,
    //   `maxProofsVerified` and the feature flags at the VERIFIER's compile time (zkprogram.js:594;
    //   the arity is measured in DreggCapability.ts's header). So a dregg turn statement has to be
    //   projected onto a FIXED-WIDTH app state chosen before any dregg proof exists, and nobody has
    //   chosen it. ⚑ Not an obstacle, but it is a decision, and it is not made.
    //   One thing that is NOT in the way, measured: the registered dregg VK declares
    //   `max_proofs_verified = N1`, the same arity as this gate's delegated slot.
    //
    // Until both close, this is a commitment, and calling it anything else would be the thing this
    // repo keeps refusing to do.
    const prev = this.receiptChain.getAndRequireEquals();
    const receipt = Poseidon.hash([
      prev,
      cap.authority,
      cap.subjectHi,
      cap.subjectLo,
      cap.effectMask,
      cap.maxTransfer,
      effectBit,
      amount.value,
      witnessTurnHi,
      witnessTurnLo,
    ]);
    this.receiptChain.set(receipt);
    this.turnsHonored.set(this.turnsHonored.getAndRequireEquals().add(1));
  }

  /**
   * ROTATE the root authority. See the file header: this is the ONLY revocation a bare vk-hash
   * policy can express, and it revokes everything at once. Signature-authorized by the zkApp key,
   * because a proof-authorized rotation would need a capability to rotate — which is a fourth verb
   * this gate does not carry.
   *
   * ⚠ It does NOT reset `receiptChain`. The history of what the OLD authority permitted is not
   * falsified by the rotation, and zeroing it would let a rotation erase a record.
   */
  @method async rotateAuthority(newRoot: Field, newAttenuator: Field) {
    this.rootAuthority.getAndRequireEquals();
    this.attenuatorProgram.getAndRequireEquals();
    newRoot.assertNotEquals(
      Field(0),
      'Field(0) is the DreggCapability root sentinel; rotating to it would make the gate honor an ' +
        'unattenuated root claim from any program',
    );
    newAttenuator.assertNotEquals(
      Field(0),
      'Field(0) is not a verification-key hash; a gate with no narrowing rule accepts any scope',
    );
    this.rootAuthority.set(newRoot);
    this.attenuatorProgram.set(newAttenuator);
  }
}
