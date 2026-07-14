/**
 * The fhEgg sealed-bid commit→reveal ceremony (the two-phase auction flow the
 * launchpad / DrEX runs).
 *
 * A sealed auction hides bids until a reveal window: the bidder first publishes
 * a binding-but-hiding COMMITMENT (`keccak256(bidder ‖ orderHash ‖ salt)`) and
 * escrows on-chain against it; at the reveal, they publish the opening
 * `(order, salt)` and anyone re-hashes to check it binds. This module is the
 * pure crypto of that ceremony — commitment/opening derivation and the EIP-712
 * `SealedBid` / `RevealBid` shapes the on-chain escrow verifies. The stateful
 * orchestration (store the opening, gate on confirm-intent, sign with the sealed
 * key) lives in the background worker.
 *
 * Everything is real keccak256 + secp256k1 (the vendored @noble primitives via
 * `./evm`); the commitment and the reveal check are self-consistent and an EVM
 * `SealedAuction` contract recomputes them identically.
 */
import { keccak256, fromHex0x, hex0x, type Eip712Domain, type Eip712Types } from "./evm";

function utf8(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

/**
 * Canonical JSON of an order (stable key order) so the commitment binds the
 * EXACT order, byte-for-byte, across commit and reveal.
 */
export function canonicalOrderJson(order: Record<string, unknown>): string {
  const keys = Object.keys(order).sort();
  const norm: Record<string, unknown> = {};
  for (const k of keys) norm[k] = order[k];
  return JSON.stringify(norm);
}

/** keccak256 of the canonical order encoding. */
export function orderHash(order: Record<string, unknown>): Uint8Array {
  return keccak256(utf8(canonicalOrderJson(order)));
}

export interface SealedCommitment {
  /** `0x…` 32-byte commitment the bidder escrows against. */
  commitment: string;
  /** `0x…` keccak of the canonical order. */
  orderHash: string;
  /** `0x…` 32-byte salt (the hiding nonce; kept in the opening). */
  salt: string;
}

/**
 * Build the sealed-bid commitment: `keccak256(bidder(20) ‖ orderHash(32) ‖
 * salt(32))`. `bidderAddress` is the escrowing EVM address; `salt` is a fresh
 * 32-byte nonce (a caller may pass one for determinism, else supply a random
 * one). The returned opening `{orderHash, salt}` + the order reproduce the
 * commitment at reveal.
 */
export function buildCommitment(
  bidderAddress: string,
  order: Record<string, unknown>,
  salt: Uint8Array,
): SealedCommitment {
  if (salt.length !== 32) throw new Error("buildCommitment: salt must be 32 bytes");
  const bidder = fromHex0x(bidderAddress);
  if (bidder.length !== 20) throw new Error("buildCommitment: bidder must be a 20-byte address");
  const oh = orderHash(order);
  const commitment = keccak256(bidder, oh, salt);
  return { commitment: hex0x(commitment), orderHash: hex0x(oh), salt: hex0x(salt) };
}

/**
 * Reveal check: recompute the commitment from the opening and confirm it binds.
 * The on-chain `revealBid` runs this exact recomputation.
 */
export function checkReveal(
  bidderAddress: string,
  order: Record<string, unknown>,
  saltHex: string,
  expectedCommitment: string,
): { ok: boolean; recomputed: string; expected: string } {
  const rebuilt = buildCommitment(bidderAddress, order, fromHex0x(saltHex));
  return {
    ok: rebuilt.commitment.toLowerCase() === expectedCommitment.toLowerCase(),
    recomputed: rebuilt.commitment,
    expected: expectedCommitment,
  };
}

/** EIP-712 domain for a launchpad `SealedAuction` escrow. */
export function sealedAuctionDomain(chainId: number, verifyingContract: string): Eip712Domain {
  return { name: "DreggSealedAuction", version: "1", chainId, verifyingContract };
}

/** The `SealedBid` commit struct the escrow's `commitBid` verifies. */
export const SEALED_BID_TYPES: Eip712Types = {
  SealedBid: [
    { name: "auctionId", type: "uint256" },
    { name: "commitment", type: "bytes32" },
    { name: "deadline", type: "uint256" },
  ],
};

/** The `RevealBid` struct the escrow's `revealBid` verifies. */
export const REVEAL_BID_TYPES: Eip712Types = {
  RevealBid: [
    { name: "auctionId", type: "uint256" },
    { name: "orderHash", type: "bytes32" },
    { name: "salt", type: "bytes32" },
  ],
};
