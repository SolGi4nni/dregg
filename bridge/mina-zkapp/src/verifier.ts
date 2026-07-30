import { ZkProgram, Field, Struct, SelfProof, Poseidon } from 'o1js';

// ---------------------------------------------------------------------------
// Public input for state transition proofs
// ---------------------------------------------------------------------------

/**
 * The public input to the recursive verifier. Each step proves a valid
 * state transition from oldRoot to newRoot at a given height. The effectsHash
 * commits to the set of effects (cell mutations, capability grants, etc.)
 * that produced the transition.
 */
export class StateTransitionInput extends Struct({
  oldRoot: Field,
  newRoot: Field,
  height: Field,
  effectsHash: Field,
}) {
  /**
   * Compute a commitment to this transition (used for deduplication).
   */
  commitment(): Field {
    return Poseidon.hash([
      this.oldRoot,
      this.newRoot,
      this.height,
      this.effectsHash,
    ]);
  }
}

// ---------------------------------------------------------------------------
// The recursive ZkProgram
// ---------------------------------------------------------------------------

/**
 * DreggVerifier: recursive proof program for dregg state transitions.
 *
 * Architecture:
 * 1. The Rust side produces a STARK proof of a state transition batch.
 * 2. The Kimchi verifier circuit (in Rust) verifies the STARK inside a
 *    Kimchi/Pickles-compatible circuit.
 * 3. That Pickles proof is what o1js actually verifies recursively.
 * 4. This ZkProgram chains those proofs together, so a single proof can
 *    attest to an arbitrarily long sequence of state transitions.
 *
 * The base case (`verifyTransition`) accepts a single transition. The
 * recursive case (`verifyChain`) chains a previous proof with a new step.
 *
 * ⚠⚠ STEPS 2–4 ABOVE DESCRIBE A PIPELINE THAT DOES NOT EXIST HERE, AND THE
 * INFERENCE BELOW THEM WAS INVALID. Corrected 2026-07-30. The removed text read:
 * "In production, the private inputs would include the actual Pickles proof from
 * the Rust side. Here, the verification is implicit: if the o1js prover can
 * produce a valid proof for this program, the underlying STARK was valid
 * (because the Pickles wrapping ensures it)."
 *
 * There is no Pickles wrapping in this file or anything it reaches, so the
 * parenthetical premise is false and the conditional it licenses is empty.
 * `verifyTransition` declares `privateInputs: []` — it consumes NO proof object
 * — and its entire constraint set is the five inequalities in its body. Any
 * party can produce a `DreggVerifier` proof for ANY four field elements. The
 * STARK→Kimchi→Pickles route this comment describes was REMOVED
 * (`bridge/src/mina.rs` header: its pickles step never verified the Kimchi proof
 * in-circuit, so the recursion was vacuous scaffolding).
 *
 * `verifyChain`'s `previousProof.verify()` IS a genuine `SelfProof` verify, so
 * the recursion mechanism works — but it chains base proofs with zero dregg
 * content, which makes the aggregate claim ("a single proof can attest to an
 * arbitrarily long sequence of state transitions") an attestation about nothing.
 *
 * `DreggVerifier` / `DreggStateProof` / `compileVerifier` have no importer
 * outside this file. The proof-gated shape lives in `DreggHeadAnchor.ts`.
 */
export const DreggVerifier = ZkProgram({
  name: 'dregg-state-verifier',
  publicInput: StateTransitionInput,

  methods: {
    /**
     * Base case: verify a single state transition.
     *
     * In the real system, this method's constraints encode the STARK
     * verification (via Pickles wrapping). The Rust bridge produces the
     * witness that satisfies these constraints.
     */
    verifyTransition: {
      privateInputs: [],
      async method(publicInput: StateTransitionInput) {
        // Structural validity: roots must be non-zero (zero = uninitialized)
        publicInput.oldRoot.assertNotEquals(Field(0));
        publicInput.newRoot.assertNotEquals(Field(0));

        // Height must be positive
        publicInput.height.assertGreaterThan(Field(0));

        // Roots must actually differ (a no-op transition is invalid)
        publicInput.oldRoot.assertNotEquals(publicInput.newRoot);

        // Effects hash must be non-zero (empty effects = no transition)
        publicInput.effectsHash.assertNotEquals(Field(0));
      },
    },

    /**
     * Recursive case: chain a previous proof with a new transition.
     *
     * Verifies:
     * - The previous proof is valid
     * - The chain is continuous (prev.newRoot == this.oldRoot)
     * - Heights are strictly increasing
     */
    verifyChain: {
      privateInputs: [SelfProof],
      async method(
        publicInput: StateTransitionInput,
        previousProof: SelfProof<StateTransitionInput, void>,
      ) {
        // Verify the previous proof is valid
        previousProof.verify();

        // Chain continuity: the previous proof's new root must be our old root
        const prevInput = previousProof.publicInput;
        prevInput.newRoot.assertEquals(publicInput.oldRoot);

        // Monotonic height: must be strictly increasing
        publicInput.height.assertGreaterThan(prevInput.height);

        // Structural validity on current step
        publicInput.newRoot.assertNotEquals(Field(0));
        publicInput.effectsHash.assertNotEquals(Field(0));
      },
    },
  },
});

// ---------------------------------------------------------------------------
// Derived types
// ---------------------------------------------------------------------------

/**
 * The proof class produced by DreggVerifier. Use this type when accepting
 * proofs in other contracts or programs.
 */
export class DreggStateProof extends ZkProgram.Proof(DreggVerifier) {}

// ---------------------------------------------------------------------------
// Verification key management
// ---------------------------------------------------------------------------

/**
 * Compile the verifier and return its verification key.
 * This must be done before any proofs can be generated or verified.
 */
export async function compileVerifier(): Promise<{ verificationKey: string }> {
  const result = await DreggVerifier.compile();
  return { verificationKey: result.verificationKey.data };
}
