/**
 * DEVICE KEY — the browser's own signing key, so a web turn carries a signature
 * THIS SERVER DID NOT MAKE.
 *
 * ## What was blocking this, and what actually was not
 *
 * The identity pages record the blocker as "in-browser derivation needs a real
 * BLAKE3 in JS, and hand-rolling BLAKE3 is forbidden here". That is TRUE and it
 * still stands — but it blocks DERIVING THE PHRASE'S KEY in the browser, which
 * is a different thing from SIGNING A TURN in the browser.
 *
 * The canonical turn message (`dreggnet-offerings/src/signed.rs::signing_message`)
 * contains no hash at all. It is a plain byte concatenation:
 *
 *   "dregg-offering-turn-v1:" | offering_key | 0x00 | session_id | 0x00
 *     | counter_le(8) | 0x00 | action.turn | 0x00 | action.arg_le(8) | 0x00
 *     | action.text-or-empty
 *
 * So signing needs Ed25519 and nothing else. No BLAKE3, no BIP39 wordlist, no
 * new dependency, and — this is the part that matters — no derivation from the
 * phrase, because THIS KEY IS NOT DERIVED FROM THE PHRASE. The browser mints its
 * own keypair; the server never sees the secret and could not reproduce it if it
 * wanted to. That is what makes `Custody::UserHeld` literally true here rather
 * than a grade we award ourselves.
 *
 * ## WHERE THE SECRET LIVES: in a key the page cannot read
 *
 * `crypto.subtle.generateKey({name:"Ed25519"}, false, ["sign"])` returns a
 * NON-EXTRACTABLE CryptoKey. It is structured-cloneable, so it is stored in
 * IndexedDB as a live key handle — never as bytes. A script on this page (an
 * injected one included) can ASK it to sign while the page is open; it cannot
 * read it, copy it, or carry it away. That property is the whole reason this is
 * WebCrypto and not the already-vendored `noble-ed25519.js`: noble would need
 * the raw seed in reachable storage, which is precisely the exposure
 * `seed_identity` rejected `localStorage` over.
 *
 * ⚑ NO FALLBACK, ON PURPOSE. A browser without WebCrypto Ed25519 (Chrome before
 * 137, Firefox before 129, Safari before 17) gets NO device key and keeps the
 * ordinary attributed path, unchanged and working. Quietly falling back to a
 * script-readable key would hand out the strong custody grade for a weak custody
 * story, which is the exact overstatement the grade exists to prevent. The page
 * says which browser it is in one sentence rather than failing silently.
 *
 * ## What this module is NOT
 *
 * It is not an identity. The 24-word phrase is still the identity; this key is a
 * device that the phrase-holder ENROLS (`POST /identity/device`), and enrolment
 * is a signature by the phrase over "this device may act as me". Revoking it is
 * the same un-link door that removes a platform link. Losing this browser loses
 * a device, never the identity.
 */

"use strict";

/** The domain tag every offering-turn signature is bound under (ASCII). */
export const TURN_SIGNING_DOMAIN = "dregg-offering-turn-v1:";

/**
 * The domain tag a finished Lean-native Descent RUN is attested under.
 *
 * ⚑ A per-RUN envelope, not a per-turn one, because the Descent never uses
 * `/act`: it plays entirely in this tab and POSTs a whole finished record to
 * `/descent/native/submit`. A turn signature has nothing to attach to on that
 * path, so the board where "it cannot be faked" is sold hardest was the one
 * lane with no signature at all.
 *
 * Disjoint from TURN_SIGNING_DOMAIN by construction: a run signature can never
 * be replayed as a turn signature or the reverse, whatever the trailing bytes.
 */
export const DESCENT_NATIVE_RUN_DOMAIN = "dregg-descent-native-run-v1:";

const DB_NAME = "dregg-device-key";
const DB_VERSION = 1;
const STORE = "keys";
/** One device key per browser profile; the record id is fixed. */
const RECORD_ID = "offering-turn-signer";

const U64_MAX = (1n << 64n) - 1n;
const I64_MIN = -(1n << 63n);
const I64_MAX = (1n << 63n) - 1n;

// ─────────────────────────────────────────────────────────────────────────────
// Capability
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Whether this browser can hold a device key at all. Checked by ACTUALLY minting
 * one rather than by sniffing a version string: Ed25519 support has shipped
 * behind flags and in partial forms, and a feature test that lies costs a player
 * a key that cannot sign.
 *
 * @returns {Promise<boolean>}
 */
export async function deviceKeysSupported() {
  if (!globalThis.crypto || !globalThis.crypto.subtle || !globalThis.indexedDB) {
    return false;
  }
  try {
    const pair = await crypto.subtle.generateKey({ name: "Ed25519" }, false, [
      "sign",
      "verify",
    ]);
    // A real sign, because generateKey succeeding and sign throwing is a shape
    // that has existed in the wild.
    const sig = await crypto.subtle.sign(
      { name: "Ed25519" },
      pair.privateKey,
      new Uint8Array([0]),
    );
    return sig.byteLength === 64;
  } catch (_) {
    return false;
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// Storage — a live CryptoKey handle, never bytes
// ─────────────────────────────────────────────────────────────────────────────

function openDb() {
  return new Promise((resolve, reject) => {
    const req = indexedDB.open(DB_NAME, DB_VERSION);
    req.onupgradeneeded = () => {
      const db = req.result;
      if (!db.objectStoreNames.contains(STORE)) {
        db.createObjectStore(STORE, { keyPath: "id" });
      }
    };
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

function tx(db, mode, run) {
  return new Promise((resolve, reject) => {
    const t = db.transaction(STORE, mode);
    const req = run(t.objectStore(STORE));
    req.onsuccess = () => resolve(req.result);
    req.onerror = () => reject(req.error);
  });
}

async function loadRecord() {
  const db = await openDb();
  try {
    return (await tx(db, "readonly", (s) => s.get(RECORD_ID))) || null;
  } finally {
    db.close();
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// The key
// ─────────────────────────────────────────────────────────────────────────────

const HEX = Array.from({ length: 256 }, (_, i) =>
  i.toString(16).padStart(2, "0"),
);

function toHex(bytes) {
  let out = "";
  for (let i = 0; i < bytes.length; i++) out += HEX[bytes[i]];
  return out;
}

/**
 * The device key this browser holds, minting one on first call.
 *
 * @returns {Promise<{publicKeyHex: string, minted: boolean} | null>} `null` when
 *   the browser cannot hold one — the caller must then leave the attributed path
 *   exactly as it was.
 */
export async function ensureDeviceKey() {
  const existing = await currentDeviceKey();
  if (existing) return { publicKeyHex: existing.publicKeyHex, minted: false };
  if (!(await deviceKeysSupported())) return null;

  const pair = await crypto.subtle.generateKey({ name: "Ed25519" }, false, [
    "sign",
    "verify",
  ]);
  // The PUBLIC half is exported (it is public); the private half never is, and
  // `false` above is what makes that structurally true rather than a promise.
  const raw = new Uint8Array(
    await crypto.subtle.exportKey("raw", pair.publicKey),
  );
  const publicKeyHex = toHex(raw);
  const db = await openDb();
  try {
    await tx(db, "readwrite", (s) =>
      s.put({
        id: RECORD_ID,
        privateKey: pair.privateKey,
        publicKeyHex,
        mintedAt: Date.now(),
      }),
    );
  } finally {
    db.close();
  }
  return { publicKeyHex, minted: true };
}

/**
 * The device key already held, or `null`. Never mints — the read a page uses to
 * decide whether to offer signing without silently creating state.
 *
 * @returns {Promise<{publicKeyHex: string, privateKey: CryptoKey} | null>}
 */
export async function currentDeviceKey() {
  try {
    const rec = await loadRecord();
    if (!rec || !rec.privateKey || !rec.publicKeyHex) return null;
    return { publicKeyHex: rec.publicKeyHex, privateKey: rec.privateKey };
  } catch (_) {
    return null;
  }
}

/**
 * Forget this browser's device key. The identity is untouched: this is "this
 * device stops being able to sign", never "delete my account". Revoking the
 * enrolment on the server is a separate, deliberate act (the un-link door), and
 * a player who only clears this side stays enrolled until they do it.
 *
 * @returns {Promise<void>}
 */
export async function forgetDeviceKey() {
  const db = await openDb();
  try {
    await tx(db, "readwrite", (s) => s.delete(RECORD_ID));
  } finally {
    db.close();
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// ⚑ THE BYTE CONTRACT — must match `signed.rs::signing_message` exactly
// ─────────────────────────────────────────────────────────────────────────────

const encoder = new TextEncoder();

function utf8(field, value) {
  const bytes = encoder.encode(value);
  // NUL HARDENING, for the reason `extension/src/offering-sign.ts` states: the
  // message separates variable-length fields with 0x00, so a field CONTAINING a
  // NUL would let two different turns encode to the same bytes and one
  // signature verify as the other. Legitimate keys, ids, verbs and text never
  // carry one.
  if (bytes.includes(0)) {
    throw new Error(field + " must not contain a zero byte");
  }
  return bytes;
}

function u64le(value, field) {
  const v = typeof value === "bigint" ? value : BigInt(value);
  if (v < 0n || v > U64_MAX) throw new Error(field + " is out of range");
  const out = new Uint8Array(8);
  new DataView(out.buffer).setBigUint64(0, v, true);
  return out;
}

function i64le(value, field) {
  const v = typeof value === "bigint" ? value : BigInt(value);
  if (v < I64_MIN || v > I64_MAX) throw new Error(field + " is out of range");
  const out = new Uint8Array(8);
  new DataView(out.buffer).setBigInt64(0, v, true);
  return out;
}

/**
 * Build the canonical signing message for one offering turn — byte-for-byte the
 * layout `signing_message` builds and `verify_signed` checks. The Rust pin test
 * (`the_canonical_signing_message_is_pinned_byte_for_byte`) and the extension's
 * TS twin carry the same hand-built vector; this is the third builder of the
 * same bytes and it is pinned the same way from the Rust side.
 *
 * ⚑ The EPOCH-BOUND variant is deliberately not built here. The user-held
 * `/act-signed` lane passes `epoch = None` (`act_signed.rs`: the epoch is bound
 * only for custodial signers), so the epoch-free domain is the correct one and
 * signing under the other would simply never verify.
 *
 * @param {{offeringKey: string, sessionId: string, counter: bigint|number|string,
 *          turn: string, arg: bigint|number|string, text?: string|null}} params
 * @returns {Uint8Array}
 */
export function signingMessage(params) {
  const parts = [
    encoder.encode(TURN_SIGNING_DOMAIN),
    utf8("the game name", params.offeringKey),
    new Uint8Array([0]),
    utf8("the session name", params.sessionId),
    new Uint8Array([0]),
    u64le(params.counter, "the move number"),
    new Uint8Array([0]),
    utf8("the move", params.turn),
    new Uint8Array([0]),
    i64le(params.arg, "the move's value"),
    new Uint8Array([0]),
    utf8("the move's text", params.text == null ? "" : params.text),
  ];
  let len = 0;
  for (const p of parts) len += p.length;
  const out = new Uint8Array(len);
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}

/**
 * Build the canonical signing message for one finished native Descent run.
 * Byte-for-byte the layout `descent_attest.rs::native_signing_message` builds
 * and re-checks; the Rust pin test carries the same hand-built vector.
 *
 * ⚑ What it covers, and what it deliberately does not:
 *
 *   daySeedHex  the WORLD, not the day's label. Two labels can name one world,
 *               and the server lands a run on whichever is already open, so
 *               signing the label would make the signature depend on an alias.
 *   rulesetId   the hash of the emitted program the run was played under.
 *   actor       the name the run is filed under. Bound because a signature that
 *               did not cover the name would let a captured run be re-filed
 *               under a different one, which is worse than not signing at all.
 *   turns       how many moves landed, which is what the board ranks on.
 *   rootHex     the run's actor-bound hash-chained journal head. THIS is how
 *               the whole move tape is covered without pushing megabytes of
 *               JSON through the signer: every landed event is chained into the
 *               root, the day-seed is in its genesis, and the server's own
 *               replay is what proves the submitted record produces exactly it.
 *
 * NOT covered: whether the moves were legal (the server replays them, and that
 * is a separate claim the run card states separately), and who discovered the
 * line (anyone may replay a run they have seen and file it honestly under their
 * own name). There is no epoch here on purpose: a run submission is
 * content-addressed and idempotent, so a captured envelope lands the identical
 * row under the identical name and there is nothing for an epoch to prevent.
 *
 * @param {{daySeedHex: string, rulesetId: string, actor: string,
 *          turns: bigint|number|string, rootHex: string}} params
 * @returns {Uint8Array}
 */
export function descentRunSigningMessage(params) {
  const parts = [
    encoder.encode(DESCENT_NATIVE_RUN_DOMAIN),
    utf8("the day", params.daySeedHex),
    new Uint8Array([0]),
    utf8("the rules", params.rulesetId),
    new Uint8Array([0]),
    utf8("the name", params.actor),
    new Uint8Array([0]),
    u64le(params.turns, "the number of moves"),
    new Uint8Array([0]),
    // The root rides LAST and unterminated: nothing follows it that a shifted
    // boundary could steal bytes from.
    utf8("the run root", params.rootHex),
  ];
  // `utf8` appends no terminator of its own, so the trailing entry above is the
  // bare root bytes and the message ends there.
  let len = 0;
  for (const p of parts) len += p.length;
  const out = new Uint8Array(len);
  let at = 0;
  for (const p of parts) {
    out.set(p, at);
    at += p.length;
  }
  return out;
}

/**
 * Sign one finished native Descent run with this browser's device key.
 *
 * @returns {Promise<{signer_pubkey_hex: string, signature_hex: string,
 *                    ruleset_id: string} | null>} `null` when this browser
 *   holds no device key, which the caller MUST treat as "post the run without
 *   an attestation" rather than as an error. A player must never lose a run
 *   because the stronger claim was unavailable.
 */
export async function signDescentRun(params) {
  const key = await currentDeviceKey();
  if (!key) return null;
  const message = descentRunSigningMessage(params);
  const signature = await crypto.subtle.sign(
    { name: "Ed25519" },
    key.privateKey,
    message,
  );
  return {
    signer_pubkey_hex: key.publicKeyHex,
    signature_hex: toHex(new Uint8Array(signature)),
    ruleset_id: params.rulesetId,
  };
}

// ─────────────────────────────────────────────────────────────────────────────
// Signing one turn
// ─────────────────────────────────────────────────────────────────────────────

/**
 * Sign one offering turn with this browser's device key.
 *
 * @returns {Promise<{actor_pubkey_hex: string, counter: string,
 *                    signature_hex: string} | null>} `null` when this browser
 *   holds no device key, which the caller must treat as "post the ordinary
 *   attributed form" rather than as an error.
 */
export async function signOfferingTurn(params) {
  const key = await currentDeviceKey();
  if (!key) return null;
  const message = signingMessage(params);
  const signature = await crypto.subtle.sign(
    { name: "Ed25519" },
    key.privateKey,
    message,
  );
  return {
    actor_pubkey_hex: key.publicKeyHex,
    counter: String(params.counter),
    signature_hex: toHex(new Uint8Array(signature)),
  };
}

/**
 * The next replay counter to sign at, for `(offering, session, this key)`.
 *
 * ⚑ The counter is a FLOOR the server enforces, not a sequence the client owns:
 * `verify_signed` admits any counter at or above the floor and then consumes it.
 * So this asks the server for its floor and takes the larger of that and this
 * browser's own high-water mark. Two windows of the same game in the same
 * browser would otherwise race to the same number and the second would be
 * refused as a replay — which is the gate working, and is still a lost move.
 *
 * @returns {Promise<bigint>}
 */
export async function nextCounter(offeringKey, sessionId, pubkeyHex) {
  const url =
    "/offerings/" +
    encodeURIComponent(offeringKey) +
    "/session/" +
    encodeURIComponent(sessionId) +
    "/next-counter?actor=" +
    encodeURIComponent(pubkeyHex);
  let floor = 0n;
  try {
    const res = await fetch(url, {
      headers: { Accept: "application/json" },
      credentials: "same-origin",
    });
    if (res.ok) {
      const body = await res.json();
      if (body && typeof body.next === "string") floor = BigInt(body.next);
    }
  } catch (_) {
    // A floor we could not read is 0, and the server refuses a stale counter
    // rather than admitting one — the failure mode is a refused move, never an
    // accepted replay.
  }
  const markKey = "dregg-counter:" + offeringKey + ":" + sessionId;
  let mark = 0n;
  try {
    const stored = localStorage.getItem(markKey);
    if (stored) mark = BigInt(stored);
  } catch (_) {}
  const next = floor > mark ? floor : mark;
  try {
    localStorage.setItem(markKey, String(next + 1n));
  } catch (_) {}
  return next;
}

/**
 * Sign and post one turn to `/act-signed`, returning the server's response so
 * the caller can swap the rendered fragment exactly as the unsigned path does.
 *
 * @returns {Promise<Response|null>} `null` when this browser cannot sign, which
 *   means "fall through to the ordinary form post".
 */
export async function postSignedTurn(offeringKey, sessionId, action) {
  const key = await currentDeviceKey();
  if (!key) return null;
  const counter = await nextCounter(offeringKey, sessionId, key.publicKeyHex);
  const signed = await signOfferingTurn({
    offeringKey,
    sessionId,
    counter,
    turn: action.turn,
    arg: action.arg,
    text: action.text,
  });
  if (!signed) return null;
  return fetch(
    "/offerings/" +
      encodeURIComponent(offeringKey) +
      "/session/" +
      encodeURIComponent(sessionId) +
      "/act-signed",
    {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "X-Fragment": "1",
        Accept: "text/html",
      },
      credentials: "same-origin",
      body: JSON.stringify({
        action: {
          turn: action.turn,
          arg: action.arg,
          text: action.text == null ? null : action.text,
          label: action.label == null ? undefined : action.label,
        },
        actor_pubkey_hex: signed.actor_pubkey_hex,
        counter: signed.counter,
        signature_hex: signed.signature_hex,
      }),
    },
  );
}
