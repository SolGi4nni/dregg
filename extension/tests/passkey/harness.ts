/**
 * In-page harness for the passkey-custody test.
 *
 * It drives the REAL modules — `PasskeyCustody` over the REAL dregg wasm signing
 * path (`derive_keypair_from_mnemonic` → `assemble_signed_turn_envelope`) — behind
 * an in-memory store. The ONLY thing "faked" is the authenticator itself, which is
 * a CDP **virtual authenticator** with the PRF/hmac-secret extension (set up in
 * run.mjs); every security-relevant step — PRF-gated wrap secret, AES-GCM wrap of
 * the mnemonic, gated unwrap, hybrid signing, fail-closed — is the shipping path.
 *
 * The page-side API is deliberately thin: enroll / sign / read-stored-blob /
 * re-derive-pubkey (an independent oracle) / a build-a-real-turn helper, plus a
 * pure wrap/sign LOGIC probe with an INJECTED PRF secret (the fallback the task
 * calls for if a PRF cannot be virtualized — and a strengthening check regardless).
 */
import {
  PasskeyCustody,
  InMemoryCustodyStore,
  wrapSeed,
  unwrapSeed,
} from "../../src/passkey";
import { publicKeyFromMnemonic, signTurnWithMnemonic } from "../../src/custody";

declare const window: any;

function hex(b: Uint8Array): string {
  let s = "";
  for (let i = 0; i < b.length; i++) s += b[i].toString(16).padStart(2, "0");
  return s;
}
function b64(b: Uint8Array): string {
  let s = "";
  for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]);
  return btoa(s);
}
function fromB64(s: string): Uint8Array {
  return Uint8Array.from(atob(s), (c) => c.charCodeAt(0));
}
/** Whether `needle` occurs contiguously inside `hay`. */
function containsSub(hay: Uint8Array, needle: Uint8Array): boolean {
  if (needle.length === 0 || needle.length > hay.length) return false;
  outer: for (let i = 0; i <= hay.length - needle.length; i++) {
    for (let j = 0; j < needle.length; j++) if (hay[i + j] !== needle[j]) continue outer;
    return true;
  }
  return false;
}

(async () => {
  const wb = window.wasm_bindgen;
  await wb("/dregg_wasm_bg.wasm");
  const wasm = wb; // wasm-bindgen exports hang off the init object

  const store = new InMemoryCustodyStore();
  const custody = new PasskeyCustody({ wasm, store, passphrase: "" });

  window.__passkey = {
    isAvailable: () => custody.isAvailable(),
    label: () => custody.label(),

    async enroll(mnemonic: string) {
      const seed = new TextEncoder().encode(mnemonic);
      const r = await custody.enroll(seed);
      const e = await store.load();
      return {
        credentialId: b64(r.credentialId),
        wrapped: { iv: b64(r.wrappedSeed.iv), ct: b64(r.wrappedSeed.ciphertext) },
        publicKey: hex(e!.publicKey),
      };
    },

    async storedBlob() {
      const e = await store.load();
      if (!e) return null;
      return {
        iv: b64(e.wrappedSeed.iv),
        ct: b64(e.wrappedSeed.ciphertext),
        cred: b64(e.credentialId),
        pub: hex(e.publicKey),
      };
    },

    async publicKey() {
      return hex(await custody.publicKey());
    },

    /** Independent oracle: re-derive the ed25519 pubkey straight from the mnemonic. */
    rederivePub(mnemonic: string) {
      return hex(publicKeyFromMnemonic(wasm, mnemonic, ""));
    },

    /**
     * App-side turn construction: build a real, normalized `Turn` (the exact
     * `cipherclerk_make_action_turn` → `sign_turn_v3` path the background worker
     * uses) and return its round-trippable `turn_bytes_json`. This is the input a
     * caller hands to `signTurn`; custody produces the envelope over it.
     */
    buildTurn(mnemonic: string) {
      const kp = wasm.derive_keypair_from_mnemonic(mnemonic, "", "dregg/0");
      const sk: Uint8Array = kp.secret_key;
      const built = wasm.cipherclerk_make_action_turn(
        JSON.stringify({
          sender_privkey: Array.from(sk),
          method: "propose_routes",
          memo_json: JSON.stringify({ routes: [] }),
        }),
      );
      const signed = wasm.sign_turn_v3(new Uint8Array(built.turn_bytes), sk, new Uint8Array(32));
      sk.fill(0);
      return b64(new Uint8Array(signed.turn_bytes_json));
    },

    async signTurn(turnB64: string) {
      const env = await custody.signTurn(fromB64(turnB64));
      return {
        bytes: b64(env.bytes),
        signer: hex(env.signer),
        len: env.bytes.length,
        signerInEnvelope: containsSub(env.bytes, env.signer),
      };
    },

    /** Sign expecting FAIL-CLOSED (e.g. after the authenticator's credential is cleared). */
    async signTurnExpectFail(turnB64: string) {
      try {
        await custody.signTurn(fromB64(turnB64));
        return { failedClosed: false, error: null };
      } catch (e: any) {
        return { failedClosed: true, error: String((e && e.message) || e) };
      }
    },

    /**
     * Pure wrap/unwrap/sign LOGIC with an INJECTED 32-byte secret (no WebAuthn).
     * Proves: the wrapped blob holds NO plaintext seed; a WRONG secret fails closed;
     * the RIGHT secret unwraps and the recovered mnemonic produces a valid hybrid
     * envelope whose signer matches the mnemonic's pubkey.
     */
    async logicTest(mnemonic: string, turnB64: string) {
      const subtle = crypto.subtle;
      const inject = crypto.getRandomValues(new Uint8Array(32));
      const seed = new TextEncoder().encode(mnemonic);
      const wrapped = await wrapSeed(subtle, inject, seed, (n) =>
        crypto.getRandomValues(new Uint8Array(n)),
      );
      const seedInBlob =
        containsSub(wrapped.ciphertext, seed) || containsSub(wrapped.iv, seed);

      let wrongFailedClosed = false;
      try {
        await unwrapSeed(subtle, crypto.getRandomValues(new Uint8Array(32)), wrapped);
      } catch {
        wrongFailedClosed = true;
      }

      const back = await unwrapSeed(subtle, inject, wrapped);
      const recovered = new TextDecoder().decode(back);
      const env = signTurnWithMnemonic(wasm, recovered, "", fromB64(turnB64));
      const expectedPub = publicKeyFromMnemonic(wasm, mnemonic, "");
      back.fill(0);
      inject.fill(0);
      return {
        seedInBlob,
        wrongFailedClosed,
        recoveredMatches: recovered === mnemonic,
        signer: hex(env.signer),
        expectedPub: hex(expectedPub),
        envLen: env.bytes.length,
      };
    },
  };

  window.__READY = true;
})().catch((e) => {
  window.__ERR = String((e && e.message) || e);
});
