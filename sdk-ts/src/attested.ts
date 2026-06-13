/**
 * **Attested query** — the light-client read surface (Noun 2's TS face).
 *
 * The Rust SDK's second noun is `AttestedHistory`: a verdict from verifying
 * ONE succinct whole-history aggregate, re-witnessing nothing. That STARK
 * verification is a Rust/wasm operation — pure TS carries no verifier. So
 * this client does the part TS CAN do honestly: it FETCHES the federation's
 * attested artifacts (the signed roots, the finalized checkpoints, and a
 * committed turn's full-turn STARK) so a caller can hand them to a verifier
 * (`@dregg/sdk/wasm`, or the Rust SDK) or trust them under the federation's
 * signature threshold.
 *
 * ## Honest scope
 *
 * - [`turnProof`] returns the proof BYTES; this client does NOT verify them.
 *   Verifying a full-turn STARK is `verify_full_turn` (Rust) — bring it to
 *   the wasm path or a node. Until a TS verifier lands
 *   (`attested-verify-in-ts`, a named follow-up), a fetched proof is
 *   evidence to be verified elsewhere, not a checked verdict.
 * - [`attestedRoots`] / [`checkpoint`] surface the FEDERATION-SIGNED state
 *   roots and finalized checkpoints. The `signatures` / `qc_votes` count is
 *   the trust signal; this client reports it but does not (yet) verify the
 *   threshold signatures in TS (`attested-verify-threshold-sig-in-ts`).
 *
 * This is the read-only twin of [`AgentRuntime`]: no signing, no key
 * material, just the node's public attestation surface.
 *
 * ```ts
 * const aq = new AttestedQuery("https://devnet.dregg.fg-goose.online");
 * const roots = await aq.attestedRoots();           // federation-signed roots
 * const cp = await aq.checkpoint();                 // latest finalized checkpoint
 * const proof = await aq.turnProof(turnHashHex);    // full-turn STARK bytes (verify elsewhere)
 * ```
 */

import { NodeClient, type NodeClientOptions } from "./client";
import { TurnProof } from "./receipt";

/** `GET /federation/roots` entry — one federation-attested state root. */
export interface AttestedRoot {
  /** Block height of the attested root. */
  height: number;
  /** The Merkle/state root at that height (hex). */
  merkle_root: string;
  /** Unix timestamp (seconds). */
  timestamp: number;
  /** Number of federation signatures backing this root (the trust signal). */
  signatures: number;
}

/** `GET /checkpoint/latest` / `/checkpoint/{height}` — a finalized checkpoint. */
export interface Checkpoint {
  height: number;
  ledger_state_root: string;
  note_tree_root: string;
  nullifier_set_root: string;
  revocation_tree_root: string;
  epoch: number;
  timestamp: number;
  /** Federation member count at this checkpoint. */
  federation_members: number;
  /** Quorum-certificate vote count finalizing it (the trust signal). */
  qc_votes: number;
}

/**
 * A read-only client over a node's public attestation surface — the
 * light-client read path. No identity, no signing.
 */
export class AttestedQuery {
  readonly node: NodeClient;

  constructor(node: NodeClient | string, opts: NodeClientOptions = {}) {
    this.node = typeof node === "string" ? new NodeClient(node, opts) : node;
  }

  /** `GET /federation/roots` — the federation-attested state roots. */
  attestedRoots(): Promise<AttestedRoot[]> {
    return this.node.getJson<AttestedRoot[]>("/federation/roots");
  }

  /** `GET /checkpoint/latest` — the latest finalized checkpoint. */
  checkpoint(): Promise<Checkpoint> {
    return this.node.getJson<Checkpoint>("/checkpoint/latest");
  }

  /** `GET /checkpoint/{height}` — the finalized checkpoint at `height`. */
  checkpointAt(height: number): Promise<Checkpoint> {
    return this.node.getJson<Checkpoint>(`/checkpoint/${height}`);
  }

  /**
   * The full-turn STARK for a committed turn (`GET /api/turn/{hash}/proof`),
   * or `undefined` while the node's prove pool is still producing it. The
   * proof is BYTES — verify it with the wasm/Rust `verify_full_turn`, not
   * here.
   */
  turnProof(turnHashHex: string): Promise<TurnProof | undefined> {
    return this.node.turnProof(turnHashHex);
  }
}
