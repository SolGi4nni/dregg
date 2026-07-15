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

// ─── The DreggLaunchpad seal (the deployed launchpad's canonical encoding) ─────
//
// `buildCommitment` above is the GENERIC ceremony: it seals an arbitrary order
// object (`keccak256(bidder ‖ keccak(canonicalJson(order)) ‖ salt)`), which is
// what a DrEX-style escrow over free-form orders wants.
//
// `chain/contracts/launchpad/DreggLaunchpad.sol` is NOT that shape. Its book is
// a typed `(price, qty)` pair and its seal is the ABI encoding
// `keccak256(abi.encode(price, qty, salt, bidder))` (`sealOf`, and the exact
// recomputation `revealBid` checks against the stored `sealedHash`). A bid
// sealed with the generic commitment can NEVER be revealed on that launchpad —
// `BidMismatch`. So a frontend driving the real launchpad must derive the seal
// the way the contract does; that is what this section provides.
//
// The two encodings are cross-checked against the contract itself by a shared
// vector: `test/sealedbid.test.mjs` and
// `chain/test/P0ParityLaunchLoop.t.sol::test_SealVector_MatchesTheExtensionDerivation`
// assert the SAME bytes32 — a drift on either side turns one of them red.

/** Left-pad a non-negative integer into a 32-byte big-endian ABI word. */
function abiWordUint(value: bigint): Uint8Array {
  if (value < 0n) throw new Error("abiWordUint: negative value");
  if (value >= 1n << 256n) throw new Error("abiWordUint: value exceeds uint256");
  const out = new Uint8Array(32);
  let v = value;
  for (let i = 31; i >= 0 && v > 0n; i--) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return out;
}

/** A 20-byte address as a 32-byte left-padded ABI word. */
function abiWordAddress(address: string): Uint8Array {
  const a = fromHex0x(address);
  if (a.length !== 20) throw new Error("abiWordAddress: address must be 20 bytes");
  const out = new Uint8Array(32);
  out.set(a, 12);
  return out;
}

/** A 32-byte value as an ABI word (bytes32 is already word-sized). */
function abiWordBytes32(value: string): Uint8Array {
  const b = fromHex0x(value);
  if (b.length !== 32) throw new Error("abiWordBytes32: must be 32 bytes");
  return b;
}

/** A sealed launchpad bid: the seal to escrow, plus the opening to keep. */
export interface LaunchpadSeal {
  /** `0x…` the `sealedHash` argument of `DreggLaunchpad.commitBid`. */
  seal: string;
  /** wei per WHOLE token. */
  price: string;
  /** whole tokens demanded. */
  qty: string;
  /** `0x…` the 32-byte hiding nonce — required to reveal; losing it forfeits the bid. */
  salt: string;
  /** The wei to escrow with `commitBid`: `price * qty` (the bidder's own maximum
   *  payment). A smaller deposit is refused at reveal (`UnderCollateralized`);
   *  the excess over the UNIFORM clearing price is refunded at settlement. */
  deposit: string;
}

/**
 * Derive the `DreggLaunchpad` sealed bid: `keccak256(abi.encode(uint256 price,
 * uint256 qty, bytes32 salt, address bidder))` — byte-identical to the
 * contract's `sealOf(price, qty, salt, bidder)`.
 *
 * The bidder escrows only `seal` during the commit window (no price, no size,
 * nothing to front-run), then reveals `(price, qty, salt)` in the reveal window;
 * the contract recomputes this hash and rejects anything that does not open the
 * commitment exactly (no late-switch).
 */
export function launchpadSeal(
  price: bigint,
  qty: bigint,
  saltHex: string,
  bidderAddress: string,
): LaunchpadSeal {
  const seal = keccak256(
    abiWordUint(price),
    abiWordUint(qty),
    abiWordBytes32(saltHex),
    abiWordAddress(bidderAddress),
  );
  return {
    seal: hex0x(seal),
    price: price.toString(),
    qty: qty.toString(),
    salt: saltHex.toLowerCase(),
    deposit: (price * qty).toString(),
  };
}

/**
 * The reveal check for a launchpad bid: recompute the seal from the opening and
 * confirm it binds. `DreggLaunchpad.revealBid` runs this exact recomputation and
 * reverts `BidMismatch` when it fails.
 */
export function checkLaunchpadReveal(
  price: bigint,
  qty: bigint,
  saltHex: string,
  bidderAddress: string,
  expectedSeal: string,
): { ok: boolean; recomputed: string; expected: string } {
  const rebuilt = launchpadSeal(price, qty, saltHex, bidderAddress);
  return {
    ok: rebuilt.seal.toLowerCase() === expectedSeal.toLowerCase(),
    recomputed: rebuilt.seal,
    expected: expectedSeal,
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
