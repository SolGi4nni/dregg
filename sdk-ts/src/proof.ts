/**
 * STARK proof generation and verification.
 *
 * Wraps the pyana-wasm STARK prover/verifier for Merkle membership claims,
 * predicate proofs, committed threshold proofs, garbled circuit comparisons,
 * anonymous membership proofs, and Schnorr signatures.
 */

import type {
  StarkProofResult,
  StarkVerifyResult,
  PredicateProofResult,
  PredicateVerifyResult,
  PredicateType,
  CommittedThresholdResult,
  CommittedThresholdVerifyResult,
  GarbledCompareResult,
  AnonymousMembershipResult,
  SchnorrKeypair,
  SchnorrSignature,
} from "./types";

/**
 * ProofEngine provides all zero-knowledge proof operations: STARK proofs,
 * predicate proofs, committed thresholds, garbled circuits, anonymous
 * membership, and Schnorr signatures.
 *
 * @example
 * ```ts
 * import { ProofEngine } from "@pyana/sdk";
 *
 * const engine = new ProofEngine(wasm);
 *
 * // Generate and verify a STARK proof
 * const proof = await engine.generateStarkProof(42, 4);
 * const valid = await engine.verifyStarkProof(proof.proof_json);
 * console.log(valid.valid); // true
 *
 * // Prove a predicate (age >= 18) without revealing exact age
 * const predProof = await engine.generatePredicateProof({
 *   predicateType: "gte",
 *   privateValue: 25,
 *   threshold: 18,
 *   attributeKey: "age",
 *   stateRoot: 12345,
 * });
 * ```
 */
export class ProofEngine {
  private wasm: typeof import("pyana-wasm");

  constructor(wasm: typeof import("pyana-wasm")) {
    this.wasm = wasm;
  }

  // ==========================================================================
  // STARK Proofs
  // ==========================================================================

  /**
   * Generate a STARK proof for a Merkle membership claim.
   *
   * Creates a proof that a leaf value is part of a Merkle tree of the
   * specified depth. The proof uses FRI-based polynomial commitments.
   *
   * @param leafValue - The leaf value (u32 field element).
   * @param depth - Merkle tree depth (2-8, will be clamped).
   * @returns The proof result with serialized proof and metrics.
   * @throws Error if proof generation fails.
   */
  async generateStarkProof(
    leafValue: number,
    depth: number
  ): Promise<StarkProofResult> {
    try {
      return this.wasm.generate_stark_proof(
        leafValue,
        depth
      ) as StarkProofResult;
    } catch (e) {
      throw new Error(`Failed to generate STARK proof: ${extractError(e)}`);
    }
  }

  /**
   * Verify a previously generated STARK proof.
   *
   * @param proofJson - The serialized proof JSON string.
   * @returns Verification result with valid/invalid status.
   * @throws Error if the proof JSON is malformed.
   */
  async verifyStarkProof(proofJson: string): Promise<StarkVerifyResult> {
    try {
      return this.wasm.verify_stark_proof(proofJson) as StarkVerifyResult;
    } catch (e) {
      throw new Error(`Failed to verify STARK proof: ${extractError(e)}`);
    }
  }

  /**
   * Tamper with a STARK proof by flipping bits. Useful for testing that
   * verification correctly rejects corrupted proofs.
   *
   * @param proofJson - The original proof JSON.
   * @returns The tampered proof JSON.
   * @throws Error if the proof is malformed.
   */
  async tamperStarkProof(proofJson: string): Promise<string> {
    try {
      return this.wasm.tamper_stark_proof(proofJson);
    } catch (e) {
      throw new Error(`Failed to tamper proof: ${extractError(e)}`);
    }
  }

  // ==========================================================================
  // Predicate Proofs
  // ==========================================================================

  /**
   * Options for generating a predicate proof.
   */
  /**
   * Generate a predicate proof for a private attribute.
   *
   * Proves a comparison (e.g., age >= 18) about a private value without
   * revealing the value itself. The proof is bound to a fact commitment
   * derived from the attribute key and state root.
   *
   * @param options - The predicate parameters.
   * @returns The predicate proof result.
   * @throws Error if the predicate is not satisfiable.
   */
  async generatePredicateProof(options: {
    /** Comparison operator. */
    predicateType: PredicateType;
    /** The secret value to prove about. */
    privateValue: number;
    /** The public threshold to compare against. */
    threshold: number;
    /** Attribute key for fact commitment derivation. */
    attributeKey: string;
    /** State root field element for binding. */
    stateRoot: number;
  }): Promise<PredicateProofResult> {
    try {
      return (this.wasm as any).generate_predicate_proof(
        options.predicateType,
        options.privateValue,
        options.threshold,
        options.attributeKey,
        options.stateRoot
      ) as PredicateProofResult;
    } catch (e) {
      throw new Error(`Failed to generate predicate proof: ${extractError(e)}`);
    }
  }

  /**
   * Verify a predicate proof.
   *
   * @param proofJson - The serialized predicate proof.
   * @param threshold - The expected threshold value.
   * @param factCommitment - The expected fact commitment.
   * @returns Whether the proof is valid.
   * @throws Error if the proof is malformed.
   */
  async verifyPredicateProof(
    proofJson: string,
    threshold: number,
    factCommitment: number
  ): Promise<PredicateVerifyResult> {
    try {
      return (this.wasm as any).verify_predicate_proof(
        proofJson,
        threshold,
        factCommitment
      ) as PredicateVerifyResult;
    } catch (e) {
      throw new Error(`Failed to verify predicate proof: ${extractError(e)}`);
    }
  }

  // ==========================================================================
  // Committed Threshold Proofs
  // ==========================================================================

  /**
   * Prove that a private value meets a committed threshold (value >= threshold)
   * without revealing either value to third parties.
   *
   * The threshold is hidden behind a Poseidon2 commitment, so the verifier
   * only learns that the check passed, not what the threshold was.
   *
   * @param value - The prover's private attribute value.
   * @param threshold - The verifier's threshold.
   * @param blinding - Randomness for the threshold commitment.
   * @returns The committed threshold proof result.
   * @throws Error if the predicate is not satisfiable (value < threshold).
   */
  async proveCommittedThreshold(
    value: number,
    threshold: number,
    blinding: number
  ): Promise<CommittedThresholdResult> {
    try {
      return (this.wasm as any).prove_committed_threshold(
        value,
        threshold,
        blinding
      ) as CommittedThresholdResult;
    } catch (e) {
      throw new Error(
        `Failed to prove committed threshold: ${extractError(e)}`
      );
    }
  }

  /**
   * Verify a committed threshold proof given the public commitments.
   *
   * @param proofJson - Serialized STARK proof.
   * @param thresholdCommitment - The Poseidon2(threshold, blinding) value.
   * @param factCommitment - The binding to token state.
   * @returns Whether the proof is valid.
   * @throws Error if the proof is malformed.
   */
  async verifyCommittedThreshold(
    proofJson: string,
    thresholdCommitment: number,
    factCommitment: number
  ): Promise<CommittedThresholdVerifyResult> {
    try {
      return (this.wasm as any).verify_committed_threshold(
        proofJson,
        thresholdCommitment,
        factCommitment
      ) as CommittedThresholdVerifyResult;
    } catch (e) {
      throw new Error(
        `Failed to verify committed threshold: ${extractError(e)}`
      );
    }
  }

  // ==========================================================================
  // Garbled Circuit Comparison
  // ==========================================================================

  /**
   * Run the garbled circuit comparison protocol (both parties simulated in-process).
   *
   * Proves `proverValue >= verifierThreshold` without the prover learning
   * the threshold. This uses a garbled circuit approach where the verifier
   * garbles a comparison circuit and the prover evaluates it.
   *
   * @param proverValue - The prover's private value.
   * @param verifierThreshold - The verifier's private threshold.
   * @returns The comparison result with pass/fail status and proof.
   */
  async garbledCompare(
    proverValue: number,
    verifierThreshold: number
  ): Promise<GarbledCompareResult> {
    try {
      return (this.wasm as any).garbled_compare(
        proverValue,
        verifierThreshold
      ) as GarbledCompareResult;
    } catch (e) {
      throw new Error(`Failed to run garbled comparison: ${extractError(e)}`);
    }
  }

  // ==========================================================================
  // Anonymous Membership
  // ==========================================================================

  /**
   * Generate a blinded ring membership proof.
   *
   * Proves that an agent is a member of a ring (set of identities) without
   * revealing which specific member they are. Uses Poseidon2 blinding for
   * unlinkability across sessions.
   *
   * @param agentIdHex - Hex-encoded 32-byte agent identity.
   * @param ringMembers - Array of hex-encoded 32-byte member identities.
   * @returns The anonymous membership proof result.
   * @throws Error if the agent is not in the ring or inputs are malformed.
   */
  async proveAnonymousMembership(
    agentIdHex: string,
    ringMembers: string[]
  ): Promise<AnonymousMembershipResult> {
    const ringJson = JSON.stringify(ringMembers);
    try {
      return (this.wasm as any).prove_anonymous_membership(
        agentIdHex,
        ringJson
      ) as AnonymousMembershipResult;
    } catch (e) {
      throw new Error(
        `Failed to prove anonymous membership: ${extractError(e)}`
      );
    }
  }

  // ==========================================================================
  // Schnorr Signatures
  // ==========================================================================

  /**
   * Generate a Schnorr keypair on the BabyBear^8 curve.
   *
   * @returns A keypair with secret key bytes and public key coordinates.
   */
  async schnorrKeygen(): Promise<SchnorrKeypair> {
    try {
      const result = (this.wasm as any).schnorr_keygen();
      return {
        secret_key: new Uint8Array(result.secret_key),
        public_key_x: result.public_key_x,
        public_key_y: result.public_key_y,
      } as SchnorrKeypair;
    } catch (e) {
      throw new Error(`Failed to generate Schnorr keypair: ${extractError(e)}`);
    }
  }

  /**
   * Sign a message with a Schnorr secret key.
   *
   * @param secretKey - The 32-byte secret key.
   * @param message - The message string to sign.
   * @returns The Schnorr signature.
   * @throws Error if the key is invalid.
   */
  async schnorrSign(
    secretKey: Uint8Array,
    message: string
  ): Promise<SchnorrSignature> {
    const keyJson = JSON.stringify({
      secret_key: Array.from(secretKey),
    });
    try {
      const result = (this.wasm as any).schnorr_sign(keyJson, message);
      return {
        r_x: result.r_x,
        r_y: result.r_y,
        s: new Uint8Array(result.s),
      } as SchnorrSignature;
    } catch (e) {
      throw new Error(`Failed to sign message: ${extractError(e)}`);
    }
  }

  /**
   * Verify a Schnorr signature.
   *
   * @param publicKeyX - BabyBear8 x-coordinate (8 u32 elements).
   * @param publicKeyY - BabyBear8 y-coordinate (8 u32 elements).
   * @param message - The message that was signed.
   * @param signature - The signature to verify.
   * @returns Whether the signature is valid.
   * @throws Error if inputs are malformed.
   */
  async schnorrVerify(
    publicKeyX: number[],
    publicKeyY: number[],
    message: string,
    signature: SchnorrSignature
  ): Promise<boolean> {
    const pkJson = JSON.stringify({
      public_key_x: publicKeyX,
      public_key_y: publicKeyY,
    });
    const sigJson = JSON.stringify({
      r_x: signature.r_x,
      r_y: signature.r_y,
      s: Array.from(signature.s),
    });
    try {
      return (this.wasm as any).schnorr_verify(
        pkJson,
        message,
        sigJson
      ) as boolean;
    } catch (e) {
      throw new Error(`Failed to verify signature: ${extractError(e)}`);
    }
  }
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
