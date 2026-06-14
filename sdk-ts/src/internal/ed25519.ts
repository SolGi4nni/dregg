/**
 * Ed25519 via @noble/ed25519 (RFC 8032; deterministic signatures).
 *
 * ONE cross-platform implementation for BOTH node and the browser — the
 * `sdk-browser-ed25519-webcrypto` follow-up (`docs/design-frontiers/WEB-FORWARD.md
 * §8 S5`). Previously this module imported `node:crypto`, which a browser ESM
 * loader cannot parse, so the WHOLE SDK was node-only. @noble/ed25519 is the
 * audited reference implementation; its signatures are byte-identical to
 * `node:crypto` (the golden key-derivation vector test pins this), so swapping to
 * it changes NO bytes and makes the full acting surface bundle for the browser.
 * No cryptography is reimplemented here — we wire noble's synchronous path (the
 * `Identity` signing flow is synchronous) by supplying its required SHA-512.
 */

import * as ed from "@noble/ed25519";
import { sha512 } from "@noble/hashes/sha512";

// noble's sync API (getPublicKey / sign / verify) needs a synchronous SHA-512.
// `@noble/hashes/sha512` provides it; wiring it once here makes the sync path
// available in every environment (node + browser), with no native dependency.
// (Idempotent: setting it more than once is harmless.)
if (!ed.etc.sha512Sync) {
  ed.etc.sha512Sync = (...messages: Uint8Array[]) => sha512(ed.etc.concatBytes(...messages));
}

/** Derive the 32-byte Ed25519 public key from a 32-byte seed. */
export function ed25519PublicKey(seed32: Uint8Array): Uint8Array {
  if (seed32.length !== 32) throw new Error("ed25519 seed must be 32 bytes");
  return ed.getPublicKey(seed32);
}

/** Sign `message` with the key derived from `seed32`; 64-byte signature. */
export function ed25519Sign(seed32: Uint8Array, message: Uint8Array): Uint8Array {
  if (seed32.length !== 32) throw new Error("ed25519 seed must be 32 bytes");
  return ed.sign(message, seed32);
}

/** Verify a 64-byte signature against a 32-byte public key. */
export function ed25519Verify(
  publicKey32: Uint8Array,
  message: Uint8Array,
  signature64: Uint8Array,
): boolean {
  if (publicKey32.length !== 32 || signature64.length !== 64) return false;
  try {
    return ed.verify(signature64, message, publicKey32);
  } catch {
    return false;
  }
}
