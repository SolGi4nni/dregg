// signTurnV3 federation-domain validation — the ONE validator both the page
// bridge and the background revalidation call (src/federation-domain.ts).
// Spec: DreggCloud docs/OWNER-LIFECYCLE-BROWSER-SEAM.md — invalid type,
// length 0/31/33, fractional, negative, and >255 values must fail BEFORE any
// confirmation or signing; a present valid value round-trips exactly.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  FEDERATION_DOMAIN_LENGTH,
  SIGN_TURN_V3_FEDERATION_DOMAIN_CAPABILITY,
  ZERO_FEDERATION_DOMAIN_HEX,
  federationDomainHex,
  validateFederationDomain,
} from './.build/federation-domain.mjs';

test('capability string is the exact v1 identifier DreggCloud gates on', () => {
  assert.equal(SIGN_TURN_V3_FEDERATION_DOMAIN_CAPABILITY, 'dregg-sign-turn-v3-federation-domain/v1');
});

test('accepts exact 32-byte Uint8Array at boundary byte values 00/7f/80/ff', () => {
  for (const fill of [0x00, 0x7f, 0x80, 0xff]) {
    const domain = new Uint8Array(FEDERATION_DOMAIN_LENGTH).fill(fill);
    const v = validateFederationDomain(domain);
    assert.equal(v.ok, true, `fill 0x${fill.toString(16)} accepted`);
    assert.deepEqual(Array.from(v.bytes), Array.from(domain), 'bytes round-trip exactly');
    const expectedHex = fill.toString(16).padStart(2, '0').repeat(32);
    assert.equal(v.hex, expectedHex, 'hex is all 64 lowercase chars');
    assert.equal(v.hex.length, 64);
    assert.equal(v.hex, v.hex.toLowerCase());
  }
});

test('accepts a plain 32-entry integer array (the post-message number[] shape)', () => {
  const arr = Array.from({ length: 32 }, (_, i) => i * 7 % 256);
  const v = validateFederationDomain(arr);
  assert.equal(v.ok, true);
  assert.deepEqual(Array.from(v.bytes), arr);
  assert.equal(v.hex, arr.map((b) => b.toString(16).padStart(2, '0')).join(''));
});

test('returned bytes are a COPY — mutating the input after validation cannot change them', () => {
  const domain = new Uint8Array(32).fill(0xaa);
  const v = validateFederationDomain(domain);
  assert.equal(v.ok, true);
  domain.fill(0x00);
  assert.equal(v.bytes[0], 0xaa, 'validated copy unaffected by later mutation');
});

test('rejects wrong lengths: 0, 31, 33 (Uint8Array and plain array)', () => {
  for (const len of [0, 31, 33]) {
    const u8 = validateFederationDomain(new Uint8Array(len));
    assert.equal(u8.ok, false, `Uint8Array length ${len} rejected`);
    assert.match(u8.error, /exactly 32 bytes/);
    const arr = validateFederationDomain(new Array(len).fill(0));
    assert.equal(arr.ok, false, `array length ${len} rejected`);
    assert.match(arr.error, /exactly 32 bytes/);
  }
});

test('rejects invalid types', () => {
  for (const bad of [null, 'ff'.repeat(32), 42, {}, new ArrayBuffer(32), new Uint16Array(32), true]) {
    const v = validateFederationDomain(bad);
    assert.equal(v.ok, false, `${Object.prototype.toString.call(bad)} rejected`);
    assert.match(v.error, /must be a Uint8Array/);
  }
});

test('rejects fractional, negative, >255, and non-number elements', () => {
  const base = () => new Array(32).fill(0);
  const cases = [
    ['fractional', 1.5],
    ['negative', -1],
    ['>255', 256],
    ['NaN', NaN],
    ['Infinity', Infinity],
    ['string element', '7'],
    ['null element', null],
  ];
  for (const [label, badByte] of cases) {
    const arr = base();
    arr[13] = badByte;
    const v = validateFederationDomain(arr);
    assert.equal(v.ok, false, `${label} rejected`);
    assert.match(v.error, /federationId\[13\]/, `${label} error names the offending index`);
  }
});

test('undefined is NOT accepted by the validator (absence is the caller default, not a valid value)', () => {
  const v = validateFederationDomain(undefined);
  assert.equal(v.ok, false);
});

test('federationDomainHex + zero constant agree', () => {
  assert.equal(federationDomainHex(new Uint8Array(32)), ZERO_FEDERATION_DOMAIN_HEX);
  assert.equal(ZERO_FEDERATION_DOMAIN_HEX.length, 64);
});
