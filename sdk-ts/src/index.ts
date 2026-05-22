/**
 * @pyana/sdk - TypeScript SDK for the pyana distributed authorization system.
 *
 * This SDK wraps the pyana-wasm module into ergonomic, type-safe APIs for:
 * - Token lifecycle (mint, attenuate, verify) via macaroon-based auth
 * - STARK proof generation and verification
 * - Merkle tree operations (membership, non-membership)
 * - Predicate proofs (ZK range/comparison proofs)
 * - Datalog authorization evaluation
 * - Full runtime simulation (agents, cells, turns, federations, intents)
 *
 * @example
 * ```ts
 * import init from "pyana-wasm";
 * import { PyanaClient } from "@pyana/sdk";
 *
 * const wasm = await init();
 * const client = new PyanaClient(wasm);
 *
 * // Mint and verify a token
 * const token = await client.wallet.mint("my-service");
 * const result = await client.wallet.verify(token.token, { action: "read" });
 *
 * // Generate a STARK proof
 * const proof = await client.proof.generateStarkProof(42, 4);
 *
 * // Run a full simulation
 * const runtime = client.createRuntime();
 * const alice = await runtime.createAgent("alice", 1000);
 * ```
 *
 * @packageDocumentation
 */

export { AgentWallet } from "./wallet";
export type { AttenuateOptions, VerifyOptions } from "./wallet";

export { TokenOps } from "./token";
export type { FoldOptions } from "./token";

export { ProofEngine } from "./proof";

export { MerkleTree } from "./merkle";

export { PredicateEvaluator } from "./predicates";

export { PyanaRuntime } from "./runtime";

export type {
  // Core token types
  MintResult,
  AttenuateResult,
  VerifyResult,
  KeyResult,
  // Proof types
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
  // Merkle types
  MerkleRootResult,
  MembershipProofResult,
  NonMembershipProofResult,
  // Datalog types
  DatalogResult,
  DatalogStep,
  DatalogFact,
  DatalogRequest,
  // Token/fold types
  FoldResult,
  IntentIdInput,
  IntentConstraint,
  // Runtime types
  AgentInfo,
  CellState,
  CellPermissions,
  CellSummary,
  TurnResultView,
  TurnAction,
  FederationInfo,
  FederationState,
  BlockResult,
  ConsensusRoundResult,
  IntentInfo,
  IntentMatchResult,
  RuntimeMintResult,
  RuntimeAttenuateResult,
  CapabilityEntry,
  CDTView,
  NoteResult,
  SpendResult,
  GrantResult,
  ChannelResult,
  TripResult,
  ChannelActiveResult,
  ConditionalResult,
  ProofCondition,
  DelegationGraph,
  ReceiptEntry,
  TreeViz,
  HeightResult,
  AuthRequired,
} from "./types";

import { AgentWallet } from "./wallet";
import { TokenOps } from "./token";
import { ProofEngine } from "./proof";
import { MerkleTree } from "./merkle";
import { PredicateEvaluator } from "./predicates";
import { PyanaRuntime } from "./runtime";

/**
 * PyanaClient is the main entry point for the SDK. It combines all subsystems
 * (wallet, proofs, merkle, predicates, runtime) into a single cohesive interface.
 *
 * @example
 * ```ts
 * import init from "pyana-wasm";
 * import { PyanaClient } from "@pyana/sdk";
 *
 * const wasm = await init();
 * const client = new PyanaClient(wasm);
 *
 * // Use individual subsystems
 * const token = await client.wallet.mint("api-gateway");
 * const proof = await client.proof.generateStarkProof(7, 3);
 * const root = await client.merkle.computeRoot(["a", "b", "c"]);
 * ```
 */
export class PyanaClient {
  /** Token minting, attenuation, and verification. */
  public readonly wallet: AgentWallet;
  /** Token state operations and BLAKE3 hashing. */
  public readonly token: TokenOps;
  /** STARK proofs, predicate proofs, signatures. */
  public readonly proof: ProofEngine;
  /** Merkle tree operations. */
  public readonly merkle: MerkleTree;
  /** Datalog authorization evaluation. */
  public readonly predicates: PredicateEvaluator;

  private readonly wasm: typeof import("pyana-wasm");

  /**
   * Create a new PyanaClient. Prefer using `PyanaClient.init()` which
   * handles async wallet creation.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param wallet - A pre-created AgentWallet instance.
   */
  constructor(wasm: typeof import("pyana-wasm"), wallet: AgentWallet) {
    this.wasm = wasm;
    this.wallet = wallet;
    this.token = new TokenOps(wasm);
    this.proof = new ProofEngine(wasm);
    this.merkle = new MerkleTree(wasm);
    this.predicates = new PredicateEvaluator(wasm);
  }

  /**
   * Initialize a PyanaClient with a fresh random wallet.
   *
   * This is the recommended way to create a client instance.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @returns A fully initialized PyanaClient.
   */
  static async init(wasm: typeof import("pyana-wasm")): Promise<PyanaClient> {
    const wallet = await AgentWallet.create(wasm);
    return new PyanaClient(wasm, wallet);
  }

  /**
   * Initialize a PyanaClient with an existing root key.
   *
   * @param wasm - The initialized pyana-wasm module.
   * @param rootKey - A 32-byte root key (Uint8Array or hex string).
   * @returns A PyanaClient using the provided key.
   */
  static fromKey(
    wasm: typeof import("pyana-wasm"),
    rootKey: Uint8Array | string
  ): PyanaClient {
    const wallet = AgentWallet.fromKey(wasm, rootKey);
    return new PyanaClient(wasm, wallet);
  }

  /**
   * Create a new PyanaRuntime for full distributed system simulation.
   *
   * The runtime provides agents, cells, turns, federations, intents,
   * notes, capabilities, and revocation channels -- all running in WASM.
   *
   * @returns A new PyanaRuntime instance.
   */
  createRuntime(): PyanaRuntime {
    return new PyanaRuntime(this.wasm);
  }
}
