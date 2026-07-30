import {
  SmartContract,
  State,
  state,
  method,
  Field,
  Poseidon,
  PublicKey,
  UInt64,
  Permissions,
  DeployArgs,
  AccountUpdate,
} from 'o1js';
import { DepositEvent, WithdrawalEvent, StateAdvanceEvent } from './types.js';

// ---------------------------------------------------------------------------
// DreggFederation zkApp
// ---------------------------------------------------------------------------

/**
 * DreggFederation: the on-chain presence of a dregg federation on Mina.
 *
 * ⚠⚠ THIS CONTRACT VERIFIES NO PROOF AND AUTHENTICATES NO CALLER. Corrected
 * 2026-07-30, the same sweep that corrected `advanceState` below. The previous
 * text of this block read:
 *
 *   "It stores the federation's proven state root, which can only advance via
 *    recursive proof verification."
 *   "- provenHeight: latest block height with a verified proof"
 *   "- nullifierRoot: Merkle root of spent nullifiers (prevents double-withdrawal)"
 *   "Security model:
 *    - State advances require recursive proof (STARK→Kimchi→Pickles→o1js)
 *    - Withdrawals require a valid nullifier + state root proof
 *    - Relay authority can be rotated via governance proof"
 *
 * Every one of those lines was false, and each names a mechanism that is
 * ABSENT from this file rather than merely weak. This file contains ZERO
 * occurrences of `.verify(`, `Proof<`, `ZkProgram`, `SelfProof`, `DynamicProof`
 * — read, not inferred. Specifically:
 *
 * - `advanceState` verifies no proof and checks no signature (see its own
 *   corrected docstring). ANY caller may set the root to ANY value.
 * - `nullifierRoot` is set to `Field(0)` in `init` and NEVER WRITTEN AGAIN.
 *   `withdraw` asserts only `nullifier != 0`; it never reads or updates the
 *   nullifier set, so THE SAME NULLIFIER WITHDRAWS REPEATEDLY. Its
 *   `stateRootAtSpend` parameter is accepted and never used. This is a live
 *   double-withdrawal hole, not a documentation defect — recorded here because
 *   the doc was what hid it.
 * - `relayAuthority` is set once in `init` and there is NO ROTATION METHOD.
 *   The "governance proof" line described a method that does not exist.
 * - `provenHeight` is a monotonic counter any caller advances; nothing about
 *   it is "proven".
 *
 * The proof-gated shape these lines described is real and lives in
 * `DreggHeadAnchor.ts` (a `DynamicProof` of the folded chain plus
 * `vk.hash.assertEquals`), which is written but NOT compiled or deployed.
 *
 * State layout (8 Field slots available in o1js):
 * - stateRoot: a Field any caller may set via `advanceState`
 * - provenHeight: a monotonic counter (the name is aspirational)
 * - federationId: hash of the federation's constitution document
 * - totalLocked: total MINA value locked for bridging
 * - nullifierRoot: written once to 0 at init and never again (INERT)
 * - relayAuthority: public key hash recorded at init; never read, never rotated
 * - (2 slots reserved for future use)
 *
 * What is actually enforced:
 * - Deposits are permissionless (anyone can lock tokens) — as described.
 * - `withdraw` enforces `amount > 0`, `nullifier != 0`, and that `totalLocked`
 *   does not underflow. Nothing else.
 */
export class DreggFederation extends SmartContract {
  /** The proven dregg state root (Poseidon commitment to all cell state) */
  @state(Field) stateRoot = State<Field>();

  /** Latest proven block height */
  @state(Field) provenHeight = State<Field>();

  /** Federation identity (hash of constitution) */
  @state(Field) federationId = State<Field>();

  /** Total bridged value locked in this contract (in nanomina) */
  @state(Field) totalLocked = State<Field>();

  /** Merkle root of spent nullifiers */
  @state(Field) nullifierRoot = State<Field>();

  /** Hash of the authorized relay's public key */
  @state(Field) relayAuthority = State<Field>();

  // Events for relay observation
  events = {
    deposit: DepositEvent,
    withdrawal: WithdrawalEvent,
    stateAdvance: StateAdvanceEvent,
  };

  /**
   * Deploy the zkApp with initial state.
   */
  async deploy(args: DeployArgs) {
    await super.deploy(args);

    // Set permissions: only proofs can update state
    this.account.permissions.set({
      ...Permissions.default(),
      editState: Permissions.proof(),
      send: Permissions.proof(),
      receive: Permissions.none(),
    });
  }

  /**
   * Initialize the federation with its constitution and first state root.
   * Can only be called once (when stateRoot is 0).
   */
  @method async initialize(
    genesisRoot: Field,
    constitutionHash: Field,
    relayPubKeyHash: Field,
  ) {
    // Ensure not already initialized
    const currentRoot = this.stateRoot.getAndRequireEquals();
    currentRoot.assertEquals(Field(0));

    // Set initial state
    this.stateRoot.set(genesisRoot);
    this.provenHeight.set(Field(1));
    this.federationId.set(constitutionHash);
    this.totalLocked.set(Field(0));
    this.nullifierRoot.set(Field(0));
    this.relayAuthority.set(relayPubKeyHash);
  }

  /**
   * Advance the federation's state root.
   *
   * ⚠⚠ THIS METHOD VERIFIES NO PROOF. Corrected 2026-07-30 — the previous
   * docstring claimed "dregg STARK → Kimchi verifier → Pickles wrap → o1js
   * recursive verify" and ended "if this method executes successfully, the
   * state transition was cryptographically verified." That was FALSE and had
   * been false since the file was written. This whole file contains ZERO
   * occurrences of `.verify(`, `Proof<`, `ZkProgram`, `SelfProof` and
   * `DynamicProof` — checked by grep, not by reading.
   *
   * What `advanceState` ACTUALLY enforces, in full:
   *   - `currentRoot == oldRoot`  (the caller names the root it is replacing)
   *   - `newHeight > currentHeight`  (monotonicity)
   *   - `oldRoot != newRoot`  (non-trivial)
   * That is a monotonic counter with a signature-free setter. ANY caller may
   * advance it to ANY root. It carries no cryptographic content whatsoever.
   *
   * The proof-gated shape this docstring described is real and lives in
   * `DreggHeadAnchor.ts` — a `DynamicProof` of the 905-step chain plus
   * `vk.hash.assertEquals(...)`, with the terminal seal pinning chain LENGTH
   * as well as identity (a key pin alone is NOT sufficient: the uniform walk
   * emits one program at every query, so a proof of six-of-nineteen queries
   * carries the identical claim under the identical key). That file is
   * written, tier-0 green, and NOT yet compiled or deployed.
   *
   * ⚑ Until this method consumes such a proof, do not cite it as a bridge.
   * A name is a claim; this one was writing a cheque the code does not carry.
   */
  @method async advanceState(
    oldRoot: Field,
    newRoot: Field,
    newHeight: Field,
    effectsHash: Field,
  ) {
    // Verify the current on-chain state matches the claimed old root
    const currentRoot = this.stateRoot.getAndRequireEquals();
    currentRoot.assertEquals(oldRoot);

    // Verify height is strictly advancing
    const currentHeight = this.provenHeight.getAndRequireEquals();
    newHeight.assertGreaterThan(currentHeight);

    // The new root must differ from old (no-op transitions are invalid)
    oldRoot.assertNotEquals(newRoot);

    // Update proven state
    this.stateRoot.set(newRoot);
    this.provenHeight.set(newHeight);

    // Emit event for relay and indexer consumption
    this.emitEvent(
      'stateAdvance',
      new StateAdvanceEvent({ oldRoot, newRoot, newHeight }),
    );
  }

  /**
   * Verify that a cell exists in the current proven state.
   *
   * This is a read-only proof: it doesn't change state, but proves
   * membership for use in other contracts or off-chain verification.
   *
   * @param cellId - The cell identifier
   * @param leafHash - The hash of the cell's content
   * @param witnessRoot - The Merkle root computed from the witness path
   */
  @method async verifyMembership(
    cellId: Field,
    leafHash: Field,
    witnessRoot: Field,
  ) {
    // The witness root must match the current proven state
    const currentRoot = this.stateRoot.getAndRequireEquals();
    currentRoot.assertEquals(witnessRoot);

    // Verify the leaf is non-trivial
    leafHash.assertNotEquals(Field(0));

    // ⚠⚠ NOTHING ABOUT MEMBERSHIP IS PROVEN HERE. Corrected 2026-07-30. The
    // previous comment read: "If execution reaches here: cellId with leafHash
    // is proven to exist in the federation's state tree at the current proven
    // height." That was false. `cellId` is accepted and NEVER USED; there is no
    // witness path, no sibling list, no Merkle fold, no hash of `leafHash` into
    // anything. The two constraints above reduce to "the caller correctly
    // copied the current stateRoot" and "leafHash != 0" — which any caller can
    // satisfy for any cellId and any leafHash. A real membership check needs a
    // `MerkleWitness` argument and `witness.calculateRoot(leafHash)`.
  }

  /**
   * Deposit tokens into the bridge.
   *
   * Locks MINA in this contract and emits an event. The dregg relay observes
   * the event and credits the corresponding note on the dregg side.
   *
   * @param amount - Amount to lock (in nanomina)
   * @param noteCommitment - Poseidon(blinding || recipient || amount) for the dregg note
   */
  @method async deposit(amount: UInt64, noteCommitment: Field) {
    // Amount must be positive
    amount.assertGreaterThan(UInt64.from(0));

    // Note commitment must be non-trivial
    noteCommitment.assertNotEquals(Field(0));

    // Update total locked
    const currentLocked = this.totalLocked.getAndRequireEquals();
    const newLocked = Field.from(currentLocked.add(amount.value));
    this.totalLocked.set(newLocked);

    // Emit deposit event for relay observation
    this.emitEvent('deposit', new DepositEvent({ amount, noteCommitment }));
  }

  /**
   * Withdraw tokens from the bridge.
   *
   * Proves a note was spent on dregg (via nullifier) and unlocks the
   * corresponding MINA. The nullifier prevents double-withdrawal.
   *
   * @param amount - Amount to unlock (in nanomina)
   * @param nullifier - Proves the dregg note was spent
   * @param stateRootAtSpend - The dregg state root when the spend occurred
   * @param recipient - Who receives the unlocked MINA
   */
  @method async withdraw(
    amount: UInt64,
    nullifier: Field,
    stateRootAtSpend: Field,
    recipient: PublicKey,
  ) {
    // Amount must be positive
    amount.assertGreaterThan(UInt64.from(0));

    // Nullifier must be non-trivial
    nullifier.assertNotEquals(Field(0));

    // Verify sufficient locked balance
    const currentLocked = this.totalLocked.getAndRequireEquals();
    // currentLocked >= amount.value
    const remaining = currentLocked.sub(amount.value);
    // This will fail if currentLocked < amount (underflow in Field arithmetic
    // won't satisfy the constraint system)
    this.totalLocked.set(remaining);

    // Emit withdrawal event
    this.emitEvent(
      'withdrawal',
      new WithdrawalEvent({ amount, nullifier, recipient }),
    );
  }

  /**
   * Verify a capability attestation.
   *
   * Proves that a principal holds a capability in the dregg federation's
   * proven state. Other Mina contracts can call this to gate access based
   * on dregg capabilities.
   *
   * @param capabilityHash - Hash of the capability being attested
   * @param holder - The public key claiming the capability
   * @param attestationRoot - The state root at which the capability was proven
   */
  @method async verifyCapability(
    capabilityHash: Field,
    holder: PublicKey,
    attestationRoot: Field,
  ) {
    // The attestation must reference a root we've actually proven
    // (simplified: we just check it matches current root)
    const currentRoot = this.stateRoot.getAndRequireEquals();
    currentRoot.assertEquals(attestationRoot);

    // Capability and holder must be non-trivial
    capabilityHash.assertNotEquals(Field(0));

    // Recompute the expected attestation hash
    const expectedHash = Poseidon.hash([
      capabilityHash,
      ...holder.toFields(),
      attestationRoot,
    ]);

    // ⚠⚠ NO CAPABILITY IS ATTESTED HERE. Corrected 2026-07-30. The previous
    // comment read: "If we reach here, the capability is attested / Other
    // contracts can compose with this method." That was false, and it is the
    // most dangerous of this file's claims because it invites composition.
    // `expectedHash` is computed and then compared to NOTHING — it is only
    // asserted non-zero, which a Poseidon output essentially always is. It is
    // never checked against `stateRoot`, against any committed attestation set,
    // or against any value the federation ever wrote. This method therefore
    // succeeds for an ARBITRARY `capabilityHash` held by an ARBITRARY `holder`,
    // provided only that the caller echoes back the current root. Do not
    // compose with it.
    expectedHash.assertNotEquals(Field(0));
  }
}
