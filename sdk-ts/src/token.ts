/**
 * Token operations: fold chains, BLAKE3 hashing, and intent ID computation.
 *
 * These wrap the WASM functions that deal with token state management,
 * content-addressed hashing, and intent lifecycle.
 */

import type { FoldResult, IntentIdInput } from "./types";

/**
 * Options for demonstrating a fold (state attenuation).
 */
export interface FoldOptions {
  /**
   * Facts in the initial state, formatted as "predicate:term1:term2".
   * @example ["service:api", "action:read", "action:write"]
   */
  facts: string[];
  /**
   * Facts to remove during attenuation.
   * @example ["action:write"]
   */
  removeFacts: string[];
}

/**
 * TokenOps provides operations on pyana token state: fold chains,
 * content-addressed hashing, and intent ID computation.
 *
 * @example
 * ```ts
 * import { TokenOps } from "@pyana/sdk";
 *
 * const ops = new TokenOps(wasm);
 *
 * // Demonstrate a fold (monotonic state reduction)
 * const fold = await ops.demonstrateFold({
 *   facts: ["service:api", "action:read", "action:write"],
 *   removeFacts: ["action:write"],
 * });
 * console.log(fold.verified); // true
 * console.log(fold.remaining_facts); // 2
 *
 * // Compute BLAKE3 hash
 * const hash = ops.blake3Hash("hello world");
 *
 * // Compute canonical intent ID
 * const id = await ops.computeIntentId({
 *   kind: "Need",
 *   actions: [{ action: "read", resource: "docs/*" }],
 *   expiry: 1716000000,
 * });
 * ```
 */
export class TokenOps {
  private wasm: typeof import("pyana-wasm");

  constructor(wasm: typeof import("pyana-wasm")) {
    this.wasm = wasm;
  }

  /**
   * Demonstrate a fold operation: create a token state, then attenuate it
   * by removing facts, showing the Merkle root transition.
   *
   * This models the core pyana attenuation primitive where tokens can only
   * monotonically lose capabilities (facts are removed, never added).
   *
   * @param options - The facts and removal list.
   * @returns Fold result with old/new roots and verification status.
   * @throws Error if the WASM call fails.
   */
  async demonstrateFold(options: FoldOptions): Promise<FoldResult> {
    const factsJson = JSON.stringify(options.facts);
    const removeJson = JSON.stringify(options.removeFacts);

    try {
      return this.wasm.demonstrate_fold(factsJson, removeJson) as FoldResult;
    } catch (e) {
      throw new Error(`Failed to demonstrate fold: ${extractError(e)}`);
    }
  }

  /**
   * Compute a BLAKE3 hash of an arbitrary string.
   *
   * Returns the 64-character hex digest. Uses the same BLAKE3 implementation
   * as the Rust backend for consistency.
   *
   * @param input - The string to hash.
   * @returns 64-character hex-encoded BLAKE3 digest.
   */
  blake3Hash(input: string): string {
    return (this.wasm as any).blake3_hash(input) as string;
  }

  /**
   * Compute the canonical intent ID using the same algorithm as the Rust
   * intent engine (postcard serialization + BLAKE3 domain-separated hash).
   *
   * This produces a deterministic 32-byte ID that matches `Intent::compute_id()`
   * in the `pyana-intent` crate.
   *
   * @param input - The intent specification.
   * @returns 64-character hex-encoded intent ID.
   * @throws Error if the intent is malformed or serialization fails.
   */
  async computeIntentId(input: IntentIdInput): Promise<string> {
    const json = JSON.stringify(input);
    try {
      return (this.wasm as any).compute_intent_id(json) as string;
    } catch (e) {
      throw new Error(`Failed to compute intent ID: ${extractError(e)}`);
    }
  }

  /**
   * Derive a keypair from a BIP39 mnemonic using pyana's BLAKE3 derivation path.
   *
   * Returns 64 bytes: first 32 are the secret key seed, last 32 are reserved
   * for the public key (computed externally with Ed25519).
   *
   * @param mnemonic - A 24-word BIP39 mnemonic.
   * @param passphrase - Optional passphrase (empty string for none).
   * @returns 64-byte Uint8Array with the derived key material.
   * @throws Error if the mnemonic is invalid.
   */
  async deriveKeypairFromMnemonic(
    mnemonic: string,
    passphrase: string = ""
  ): Promise<Uint8Array> {
    try {
      return new Uint8Array(
        (this.wasm as any).derive_keypair_from_mnemonic(mnemonic, passphrase)
      );
    } catch (e) {
      throw new Error(`Failed to derive keypair: ${extractError(e)}`);
    }
  }
}

function extractError(e: unknown): string {
  if (e instanceof Error) return e.message;
  return String(e);
}
