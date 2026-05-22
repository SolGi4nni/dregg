/**
 * Merkle tree operations: root computation, membership proofs, and
 * non-membership proofs using pyana's 4-ary BLAKE3 Merkle tree.
 */

import type {
  MerkleRootResult,
  MembershipProofResult,
  NonMembershipProofResult,
} from "./types";

/**
 * MerkleTree provides operations on pyana's authenticated data structure:
 * computing roots from leaf sets, proving membership, and proving non-membership.
 *
 * All operations use the same BLAKE3-based 4-ary Merkle tree as the Rust backend.
 *
 * @example
 * ```ts
 * import { MerkleTree } from "@pyana/sdk";
 *
 * const tree = new MerkleTree(wasm);
 *
 * const leaves = ["alice", "bob", "carol"];
 * const root = await tree.computeRoot(leaves);
 * console.log(root.root_hex);
 *
 * const proof = await tree.proveMembership(leaves, "bob");
 * console.log(proof.is_member); // true
 *
 * const nonProof = await tree.proveNonMembership(leaves, "dave");
 * console.log(nonProof.proven_absent); // true
 * ```
 */
export class MerkleTree {
  private wasm: typeof import("pyana-wasm");

  constructor(wasm: typeof import("pyana-wasm")) {
    this.wasm = wasm;
  }

  /**
   * Compute the Merkle root of a set of leaf strings.
   *
   * Each leaf is hashed as a unary fact with predicate "leaf" and the
   * string as the term, matching the FactSet representation.
   *
   * @param leaves - Array of leaf strings.
   * @returns The root hash and leaf count.
   * @throws Error if the input is invalid.
   */
  async computeRoot(leaves: string[]): Promise<MerkleRootResult> {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.compute_merkle_root(leavesJson) as MerkleRootResult;
    } catch (e) {
      throw new Error(`Failed to compute Merkle root: ${extractError(e)}`);
    }
  }

  /**
   * Generate a Merkle membership proof for a specific leaf.
   *
   * Proves that `targetLeaf` is a member of the set defined by `leaves`.
   * The proof consists of sibling hashes along the path from the leaf to the root.
   *
   * @param leaves - All leaves in the tree.
   * @param targetLeaf - The leaf to prove membership for.
   * @returns Membership proof result with the root and verification status.
   * @throws Error if the WASM call fails.
   */
  async proveMembership(
    leaves: string[],
    targetLeaf: string
  ): Promise<MembershipProofResult> {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.merkle_membership_proof(
        leavesJson,
        targetLeaf
      ) as MembershipProofResult;
    } catch (e) {
      throw new Error(
        `Failed to generate membership proof: ${extractError(e)}`
      );
    }
  }

  /**
   * Generate a Merkle non-membership proof for a leaf NOT in the set.
   *
   * Proves that `absentLeaf` is NOT a member of the set. This is used
   * for revocation checks and negative authorization.
   *
   * @param leaves - All leaves in the tree.
   * @param absentLeaf - The leaf to prove absence for.
   * @returns Non-membership proof result.
   * @throws Error if the WASM call fails.
   */
  async proveNonMembership(
    leaves: string[],
    absentLeaf: string
  ): Promise<NonMembershipProofResult> {
    const leavesJson = JSON.stringify(leaves);
    try {
      return this.wasm.merkle_non_membership_proof(
        leavesJson,
        absentLeaf
      ) as NonMembershipProofResult;
    } catch (e) {
      throw new Error(
        `Failed to generate non-membership proof: ${extractError(e)}`
      );
    }
  }
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
