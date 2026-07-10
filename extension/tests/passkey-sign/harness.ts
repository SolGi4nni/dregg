/**
 * In-page harness for the SIGN-PATH-THROUGH-CustodyProvider test.
 *
 * It drives the REAL resolution seam (`../../src/custody-resolve`.resolveCustody)
 * over the REAL providers (`MnemonicCustody` / `SeedCustody` / `PasskeyCustody`) and
 * the REAL dregg wasm signing path — the exact chain `background.ts` now calls to
 * produce the `SignedTurn` envelope it POSTs. The ONLY faked thing is the
 * authenticator (a CDP virtual authenticator with PRF, set up in run.mjs).
 *
 * The page-side API exposes:
 *   • buildTurn — construct a real normalized `Turn` (turn_bytes_json), the input a
 *     caller hands the sign path;
 *   • directEnvelope — the OLD path: `assemble_signed_turn_envelope(turn, seed)`;
 *   • resolveExtensionSign — resolve the EXTENSION provider (MnemonicCustody when the
 *     mnemonic re-derives, else SeedCustody) and sign; returns tier + envelope;
 *   • enrollPasskey / resolvePasskeySign — enroll a passkey and resolve+sign through
 *     the PasskeyCustody tier (extension-less);
 *   • resolveNoCustody — resolve with NO extension + NO passkey → tier "none",
 *     provider null; a write must fail closed;
 *   • deriveSeed / rederivePub — independent oracles.
 */
import {
  MnemonicCustody,
  SeedCustody,
  publicKeyFromMnemonic,
} from "../../src/custody";
import {
  PasskeyCustody,
  InMemoryCustodyStore,
} from "../../src/passkey";
import { resolveCustody } from "../../src/custody-resolve";

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
/** Length of the longest common byte prefix of `a` and `b`. */
function lcp(a: Uint8Array, b: Uint8Array): number {
  const n = Math.min(a.length, b.length);
  let i = 0;
  while (i < n && a[i] === b[i]) i++;
  return i;
}

(async () => {
  const wb = window.wasm_bindgen;
  await wb("/dregg_wasm_bg.wasm");
  const wasm = wb;

  // A shared passkey store so enroll + resolve see the same enrollment.
  const passkeyStore = new InMemoryCustodyStore();

  function deriveSeedBytes(mnemonic: string): Uint8Array {
    const kp = wasm.derive_keypair_from_mnemonic(mnemonic, "", "dregg/0");
    const sk = new Uint8Array(kp.secret_key);
    kp.secret_key.fill(0);
    return sk;
  }
  function derivePubBytes(mnemonic: string): Uint8Array {
    return publicKeyFromMnemonic(wasm, mnemonic, "");
  }

  window.__sign = {
    /** Build a real normalized Turn (turn_bytes_json) the way background.ts does. */
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

    rederivePub(mnemonic: string) {
      return hex(derivePubBytes(mnemonic));
    },
    deriveSeed(mnemonic: string) {
      return hex(deriveSeedBytes(mnemonic));
    },

    /** The OLD direct path: assemble_signed_turn_envelope(turn, seed). */
    directEnvelope(mnemonic: string, turnB64: string) {
      const seed = deriveSeedBytes(mnemonic);
      const env: Uint8Array = wasm.assemble_signed_turn_envelope(fromB64(turnB64), seed);
      seed.fill(0);
      return b64(new Uint8Array(env));
    },

    /**
     * Resolve the EXTENSION provider and sign through the seam. `withMnemonic`
     * controls whether the mnemonic is offered (→ MnemonicCustody) or withheld
     * (→ byte-exact SeedCustody). Returns the resolved tier + envelope + signer.
     */
    async resolveExtensionSign(mnemonic: string, turnB64: string, withMnemonic: boolean) {
      const seed = deriveSeedBytes(mnemonic);
      const pub = derivePubBytes(mnemonic);
      const resolved = await resolveCustody({
        wasm,
        extension: {
          secretKey: seed,
          publicKey: pub,
          getMnemonic: withMnemonic
            ? async () => ({ mnemonic, passphrase: "" })
            : undefined,
        },
        passkeyStore,
      });
      if (!resolved.provider) {
        seed.fill(0);
        return { tier: resolved.tier, provider: false };
      }
      const env = await resolved.provider.signTurn(fromB64(turnB64));
      seed.fill(0);
      return {
        tier: resolved.tier,
        provider: true,
        label: resolved.provider.label(),
        env: b64(env.bytes),
        signer: hex(env.signer),
        signerInEnvelope: containsSub(env.bytes, env.signer),
        len: env.bytes.length,
      };
    },

    /**
     * Resolve a provider with a WRONG mnemonic-vs-pubkey (simulating a
     * BIP39-passphrase wallet): the phrase does not re-derive to the identity, so
     * resolution must fall back to SeedCustody — still byte-exact for the seed.
     */
    async resolveMismatchedMnemonic(mnemonic: string, turnB64: string) {
      const seed = deriveSeedBytes(mnemonic);
      const pub = derivePubBytes(mnemonic);
      const resolved = await resolveCustody({
        wasm,
        extension: {
          secretKey: seed,
          publicKey: pub,
          // A DIFFERENT (still valid) phrase → derives to a different key.
          getMnemonic: async () => ({ mnemonic: WRONG_MNEMONIC, passphrase: "" }),
        },
        passkeyStore,
      });
      const label = resolved.provider ? resolved.provider.label() : null;
      const env = resolved.provider ? await resolved.provider.signTurn(fromB64(turnB64)) : null;
      seed.fill(0);
      return { tier: resolved.tier, label, env: env ? b64(env.bytes) : null };
    },

    /** Enroll a passkey (PRF-wrapped) over the mnemonic — the extension-less floor. */
    async enrollPasskey(mnemonic: string) {
      const pk = new PasskeyCustody({ wasm, store: passkeyStore, passphrase: "" });
      const r = await pk.enroll(new TextEncoder().encode(mnemonic));
      const e = await passkeyStore.load();
      return { publicKey: hex(e!.publicKey), credentialId: b64(r.credentialId) };
    },

    /**
     * Resolve with NO extension material (extension-less) and sign through the
     * resolved PASSKEY provider. This is the whole point: an extension-less person
     * signs a real turn with their passkey via the SAME seam.
     */
    async resolvePasskeySign(turnB64: string) {
      const resolved = await resolveCustody({ wasm, passkeyStore });
      if (!resolved.provider) return { tier: resolved.tier, provider: false };
      const env = await resolved.provider.signTurn(fromB64(turnB64));
      return {
        tier: resolved.tier,
        provider: true,
        label: resolved.provider.label(),
        env: b64(env.bytes),
        signer: hex(env.signer),
        signerInEnvelope: containsSub(env.bytes, env.signer),
        len: env.bytes.length,
      };
    },

    /** Resolve with NO custody at all → tier "none", provider null (fail-closed). */
    async resolveNoCustody(turnB64: string) {
      const emptyStore = new InMemoryCustodyStore();
      const resolved = await resolveCustody({ wasm, passkeyStore: emptyStore });
      let failedClosed = false;
      let error: string | null = null;
      if (!resolved.provider) {
        failedClosed = true;
      } else {
        // Should not happen; if a provider were returned, exercise fail-closed anyway.
        try {
          await resolved.provider.signTurn(fromB64(turnB64));
        } catch (e: any) {
          failedClosed = true;
          error = String((e && e.message) || e);
        }
      }
      return { tier: resolved.tier, provider: !!resolved.provider, failedClosed, error };
    },

    /** Longest-common-prefix of two base64 envelopes (classical-perimeter check). */
    lcp(aB64: string, bB64: string) {
      const a = fromB64(aB64);
      const b = fromB64(bB64);
      return { lcp: lcp(a, b), aLen: a.length, bLen: b.length };
    },
  };

  window.__READY = true;
})().catch((e) => {
  window.__ERR = String((e && e.message) || e);
});

// A second valid all-different BIP39 mnemonic (checksum-valid) for the
// wallet-mismatch fallback probe; derives to a DIFFERENT dregg key.
const WRONG_MNEMONIC =
  "legal winner thank year wave sausage worth useful legal winner thank year " +
  "wave sausage worth useful legal winner thank year wave sausage worth title";
