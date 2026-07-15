import test from 'node:test';
import assert from 'node:assert/strict';

import {
  launchpadSeal,
  checkLaunchpadReveal,
  buildCommitment,
  checkReveal,
} from './.build/sealedbid.mjs';

// ─── The cross-language seal vector ────────────────────────────────────────────
//
// This EXACT constant is asserted on the contract side by
// `chain/test/P0ParityLaunchLoop.t.sol::test_SealVector_MatchesTheExtensionDerivation`
// (`pad.sealOf(5 gwei, 400, 0xd1e55ed, 0xA11CE)`). The frontend seals a bid and
// the launchpad recomputes it at `commitBid`/`revealBid`: if these two
// derivations ever drift apart, no honest bid can be revealed (`BidMismatch`),
// so both sides pin the same bytes and either drift turns one of them red.
const BIDDER = '0x00000000000000000000000000000000000A11CE';
const PRICE = 5000000000n; // 5 gwei per whole token
const QTY = 400n;
const SALT = '0x000000000000000000000000000000000000000000000000000000000d1e55ed';
const SEAL_VECTOR = '0xc9b84c4f878aeb4b76a6ffa62d14611a5226a9d4015a9eb4818aa04db238c0bb';

test('launchpadSeal reproduces the DreggLaunchpad.sealOf vector byte-for-byte', () => {
  const s = launchpadSeal(PRICE, QTY, SALT, BIDDER);
  assert.equal(s.seal, SEAL_VECTOR);
});

test('the sealed bid carries the escrow the launchpad requires (price * qty)', () => {
  const s = launchpadSeal(PRICE, QTY, SALT, BIDDER);
  // `revealBid` reverts `UnderCollateralized` if deposit < price * qty.
  assert.equal(s.deposit, (PRICE * QTY).toString());
  assert.equal(s.price, PRICE.toString());
  assert.equal(s.qty, QTY.toString());
});

test('the reveal binds: the committed opening checks, a switched bid does not', () => {
  const s = launchpadSeal(PRICE, QTY, SALT, BIDDER);

  // Honest pole: the opening the bidder committed to reveals.
  assert.equal(checkLaunchpadReveal(PRICE, QTY, SALT, BIDDER, s.seal).ok, true);

  // NO LATE-SWITCH: bidding 9 gwei after seeing the book does not open the seal.
  assert.equal(checkLaunchpadReveal(9000000000n, QTY, SALT, BIDDER, s.seal).ok, false);
  // …nor a different size, salt, or bidder.
  assert.equal(checkLaunchpadReveal(PRICE, 401n, SALT, BIDDER, s.seal).ok, false);
  assert.equal(
    checkLaunchpadReveal(PRICE, QTY, '0x' + '11'.repeat(32), BIDDER, s.seal).ok,
    false,
  );
  assert.equal(
    checkLaunchpadReveal(PRICE, QTY, SALT, '0x00000000000000000000000000000000000B0B00', s.seal).ok,
    false,
  );
});

test('the seal hides the bid: a 1-wei price difference is undetectable from the seal', () => {
  const a = launchpadSeal(PRICE, QTY, SALT, BIDDER);
  const b = launchpadSeal(PRICE + 1n, QTY, SALT, BIDDER);
  assert.notEqual(a.seal, b.seal);
  // Both are opaque 32-byte digests — the commit window publishes only this.
  assert.match(a.seal, /^0x[0-9a-f]{64}$/);
  assert.match(b.seal, /^0x[0-9a-f]{64}$/);
});

test('a bidder is bound to their own seal: the address is inside the commitment', () => {
  // The launchpad seals `bidder` in, so a seal cannot be replayed by someone
  // else (`revealBid` recomputes with `msg.sender`).
  const mine = launchpadSeal(PRICE, QTY, SALT, BIDDER);
  const theirs = launchpadSeal(PRICE, QTY, SALT, '0x00000000000000000000000000000000000B0B00');
  assert.notEqual(mine.seal, theirs.seal);
});

test('the generic order commitment is a DIFFERENT scheme and is not launchpad-valid', () => {
  // `buildCommitment` seals a free-form order object; `launchpadSeal` seals the
  // launchpad's typed (price, qty) ABI encoding. They are not interchangeable —
  // this asserts the distinction the module documents, so nobody wires the
  // generic one into `commitBid` and gets `BidMismatch` on-chain.
  const generic = buildCommitment(BIDDER, { price: PRICE.toString(), qty: QTY.toString() }, new Uint8Array(32).fill(0xab));
  const typed = launchpadSeal(PRICE, QTY, '0x' + 'ab'.repeat(32), BIDDER);
  assert.notEqual(generic.commitment, typed.seal);

  // …and the generic ceremony still binds on its own terms (unchanged).
  const ok = checkReveal(BIDDER, { price: PRICE.toString(), qty: QTY.toString() }, generic.salt, generic.commitment);
  assert.equal(ok.ok, true);
});

test('malformed inputs fail closed', () => {
  assert.throws(() => launchpadSeal(-1n, QTY, SALT, BIDDER), /negative/);
  assert.throws(() => launchpadSeal(1n << 256n, QTY, SALT, BIDDER), /uint256/);
  assert.throws(() => launchpadSeal(PRICE, QTY, '0xdead', BIDDER), /32 bytes/);
  assert.throws(() => launchpadSeal(PRICE, QTY, SALT, '0xdead'), /20 bytes/);
});
