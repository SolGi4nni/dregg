import { ArtifactRefusal } from "./poag1.js";
import { STATEMENT_SCHEMA, slotStatementMessage } from "./slot-statement.js";

/**
 * **KEEP THE OPENING YOU WERE SHOWN.**
 *
 * Every Path of Angels descriptor declares `instance.commitment.opened_after:
 * "slot-close"` — the promise that the commitment you are handed before you play
 * is opened afterwards, so you can check the instance you were judged against was
 * fixed in advance. `hidden-instance.js` REFUSES any descriptor that does not say
 * it, and `schema.json` pins the opening as `["slot", "slot_secret"]` under
 * `verify: "commit(slot_secret, slot) == commitment"`.
 *
 * That promise is only worth something if the commitment survives the session.
 * Until this module it did not: `loadSlotState` verified the curator's Ed25519
 * signature and then returned `{state, slot, missionId, commitment,
 * consensusFinality}` — **dropping the curator key and the signature on the
 * floor**. A player who verified an opening at 03:00 had, by 03:05, no evidence
 * they had done so, and nothing they retained could later be checked against
 * anything. Comparing a revealed secret against a commitment the same node hands
 * you at reveal time proves only that the node can do arithmetic.
 *
 * So: at the moment the signature verifies, write the whole opening down.
 *
 * # ⚠ FIRST SEEN WINS, and a disagreement is an ALARM
 *
 * The store is write-once per `(authority, slot)`. This is the load-bearing
 * property, not a caching nicety. If the page overwrote the receipt on every
 * load, an operator who swapped the commitment mid-slot would silently replace
 * the very evidence of the swap — the retained copy would always agree with the
 * served one, and the check would be vacuous by construction.
 *
 * Because it does not overwrite, a served opening that disagrees with the
 * retained one is caught IMMEDIATELY, while the slot is still live and long
 * before any reveal: [`retainSlotOpening`] returns `equivocation`. That is a
 * stronger detector than the reveal itself, and it costs one comparison.
 *
 * # ⚠ What this module deliberately does NOT do
 *
 * It does not check that a revealed secret opens a commitment. That is
 * `HiddenInstance.commit`, a Poseidon2-BabyBear sponge **authored in Lean**, and
 * this page has no copy of it — deliberately. A JavaScript reimplementation would
 * be a second, unproven sponge, and a player comparing the operator's claim
 * against a browser's guess at the same function has verified nothing. The sponge
 * step runs in `dregg-node poa-verify-slot-reveal`, which calls the same Lean
 * export the judge does.
 *
 * What the browser CAN do without a sponge, it does here: confirm the reveal is
 * about your slot, and that its commitment is byte-identical to the one you
 * retained before playing, and that the curator signed it. Those catch a
 * substitution. Only the sponge check catches a secret that is not the committed
 * one, and [`checkRevealAgainstReceipt`] says so in its result rather than
 * implying completeness.
 */

export const RECEIPT_SCHEMA = "POA-SLOT-OPENING-RECEIPT-1";
export const REVEAL_FORMAT = "POA-SIGNAL-SLOT-REVEAL-1";
export { STATEMENT_SCHEMA };
export const RECEIPTS_STORAGE_KEY = "poa.slot.openings.v1";

/** How many receipts to keep. Oldest by `recorded_at` are dropped past this. */
const RECEIPT_LIMIT = 64;

const HEX_32 = /^[0-9a-f]{64}$/;
const HEX_64 = /^[0-9a-f]{128}$/;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, expected, at) {
  refuse(object(value), "receipt-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    "receipt-shape",
    `${at} has an unknown or missing field; the exact set is: ${wanted.join(", ")}`,
  );
}

/** The storage slot one opening is filed under. */
export function receiptKey(authorityId, slot) {
  return `${authorityId}:${slot}`;
}

/**
 * Build the retained document.
 *
 * The shape is EXACTLY what `dregg-node poa-verify-slot-reveal --opening` parses
 * (`node/src/poa_slot_reveal_verify.rs`, `#[serde(deny_unknown_fields)]`), so a
 * player exports this file and feeds it straight to the verifier. Adding a field
 * here without adding it there makes every exported receipt unreadable.
 *
 * `recorded_at` is the player's own note to themselves. It is unsigned, nothing
 * verifies it, and the verifier ignores it — an ISO timestamp a browser wrote is
 * not evidence of when anything happened. It is here so a person reading their
 * own file can tell which session it belongs to.
 */
export function buildSlotOpeningReceipt(opening, recordedAt = new Date().toISOString()) {
  refuse(object(opening) && object(opening.statement), "receipt-shape", "an opening needs a statement");
  const statement = opening.statement;
  refuse(typeof statement.authorityId === "string" && HEX_32.test(statement.authorityId), "receipt-authority", "the opening names an invalid authority");
  refuse(Number.isSafeInteger(statement.missionId) && statement.missionId >= 0, "receipt-mission", "the opening names an invalid mission");
  refuse(Number.isSafeInteger(statement.slot) && statement.slot >= 0, "receipt-slot", "the opening names an invalid slot");
  refuse(typeof statement.commitment === "string" && HEX_32.test(statement.commitment), "receipt-commitment", "the opening names an invalid commitment");
  refuse(typeof opening.curatorKey === "string" && HEX_32.test(opening.curatorKey), "receipt-curator", "the opening names an invalid curator key");
  refuse(typeof opening.signature === "string" && HEX_64.test(opening.signature), "receipt-signature", "the opening carries an invalid signature");
  refuse(typeof recordedAt === "string" && recordedAt.length > 0 && recordedAt.length <= 64, "receipt-recorded-at", "recorded_at must be a short string");

  return Object.freeze({
    schema: RECEIPT_SCHEMA,
    statement: Object.freeze({
      schema: STATEMENT_SCHEMA,
      authority_id: statement.authorityId,
      mission_id: statement.missionId,
      slot: statement.slot,
      commitment: statement.commitment,
    }),
    curator_key: opening.curatorKey,
    signature: opening.signature,
    recorded_at: recordedAt,
  });
}

/** Is this a well-formed receipt? Anything else is dropped, never repaired. */
function validReceipt(value) {
  if (!object(value)) return false;
  const keys = Object.keys(value).sort();
  const wanted = ["curator_key", "recorded_at", "schema", "signature", "statement"];
  if (keys.length !== wanted.length || !keys.every((key, index) => key === wanted[index])) return false;
  if (value.schema !== RECEIPT_SCHEMA) return false;
  if (!object(value.statement)) return false;
  const inner = Object.keys(value.statement).sort();
  const innerWanted = ["authority_id", "commitment", "mission_id", "schema", "slot"];
  if (inner.length !== innerWanted.length || !inner.every((key, index) => key === innerWanted[index])) return false;
  if (value.statement.schema !== STATEMENT_SCHEMA) return false;
  if (typeof value.statement.authority_id !== "string" || !HEX_32.test(value.statement.authority_id)) return false;
  if (typeof value.statement.commitment !== "string" || !HEX_32.test(value.statement.commitment)) return false;
  if (!Number.isSafeInteger(value.statement.mission_id) || value.statement.mission_id < 0) return false;
  if (!Number.isSafeInteger(value.statement.slot) || value.statement.slot < 0) return false;
  if (typeof value.curator_key !== "string" || !HEX_32.test(value.curator_key)) return false;
  if (typeof value.signature !== "string" || !HEX_64.test(value.signature)) return false;
  return typeof value.recorded_at === "string" && value.recorded_at.length > 0;
}

function readAll(storage) {
  if (!storage) return {};
  let raw;
  try { raw = storage.getItem(RECEIPTS_STORAGE_KEY); } catch { return {}; }
  if (typeof raw !== "string" || raw.length === 0) return {};
  let parsed;
  try { parsed = JSON.parse(raw); } catch { return {}; }
  if (!object(parsed)) return {};
  const clean = {};
  for (const [key, value] of Object.entries(parsed)) {
    if (validReceipt(value)) clean[key] = value;
  }
  return clean;
}

function writeAll(storage, receipts) {
  if (!storage) return false;
  let entries = Object.entries(receipts);
  if (entries.length > RECEIPT_LIMIT) {
    // Drop the oldest by the player's own note. It is not evidence, but it is a
    // fine eviction order, and evicting the NEWEST would throw away the receipt
    // for the session most likely still in play.
    entries = entries
      .sort(([, a], [, b]) => String(a.recorded_at).localeCompare(String(b.recorded_at)))
      .slice(entries.length - RECEIPT_LIMIT);
  }
  try {
    storage.setItem(RECEIPTS_STORAGE_KEY, JSON.stringify(Object.fromEntries(entries)));
    return true;
  } catch {
    return false;
  }
}

/** The receipt retained for one slot, or `null`. */
export function loadSlotOpeningReceipt(authorityId, slot, storage = globalThis.localStorage) {
  const found = readAll(storage)[receiptKey(authorityId, slot)];
  return found ? Object.freeze(found) : null;
}

/** Every retained receipt, newest note first. For an "what have I kept?" view. */
export function listSlotOpeningReceipts(storage = globalThis.localStorage) {
  return Object.values(readAll(storage))
    .sort((a, b) => String(b.recorded_at).localeCompare(String(a.recorded_at)))
    .map((receipt) => Object.freeze(receipt));
}

/**
 * **Retain a verified opening — write-once.**
 *
 * Call this only AFTER the curator signature has verified. Storing an unverified
 * opening would retain the attacker's document as the trusted baseline, which
 * inverts the whole point.
 *
 * Returns one of:
 * * `{state: "recorded", receipt}` — first sighting, now written down;
 * * `{state: "retained", receipt}` — already held, byte-identical, nothing to do;
 * * `{state: "equivocation", retained, served}` — ⚠ THE ALARM. The node served a
 *   different opening for a slot you already hold one for. The retained copy is
 *   NOT replaced. Two different commitments for one slot means at most one of
 *   them was ever committed to, and a player seeing this should not play;
 * * `{state: "unstored", receipt}` — storage refused the write (private mode, quota).
 *   The receipt is still returned so it can be exported by hand; it just will not
 *   survive the tab, and a player who cares must download it.
 */
export function retainSlotOpening(opening, { storage = globalThis.localStorage, recordedAt } = {}) {
  const receipt = buildSlotOpeningReceipt(opening, recordedAt ?? new Date().toISOString());
  const key = receiptKey(receipt.statement.authority_id, receipt.statement.slot);
  const all = readAll(storage);
  const held = all[key];

  if (held) {
    const same =
      held.statement.commitment === receipt.statement.commitment &&
      held.statement.mission_id === receipt.statement.mission_id &&
      held.curator_key === receipt.curator_key &&
      held.signature === receipt.signature;
    if (same) return Object.freeze({ state: "retained", receipt: Object.freeze(held) });
    // ⚠ DO NOT OVERWRITE. The retained copy is the evidence.
    return Object.freeze({
      state: "equivocation",
      retained: Object.freeze(held),
      served: receipt,
    });
  }

  all[key] = receipt;
  const stored = writeAll(storage, all);
  return Object.freeze({ state: stored ? "recorded" : "unstored", receipt });
}

/** Parse a `POA-SIGNAL-SLOT-REVEAL-1` served by the node. Shape only. */
export function parseRevealDocument(value, authorityId) {
  exactKeys(
    value,
    ["format", "authority_id", "slot", "state", "open_slot", "opening", "slot_secret", "consensus_finality"],
    "slot reveal",
  );
  refuse(value.format === REVEAL_FORMAT, "reveal-format", `unsupported slot reveal format: ${value.format}`);
  refuse(value.authority_id === authorityId, "reveal-authority", "the slot reveal is for another authority");
  refuse(Number.isSafeInteger(value.slot) && value.slot >= 0, "reveal-slot", "the slot reveal names an invalid slot");
  refuse(["revealed", "still_open", "unknown"].includes(value.state), "reveal-state", `unknown slot reveal state: ${value.state}`);
  refuse(value.open_slot === null || (Number.isSafeInteger(value.open_slot) && value.open_slot >= 0), "reveal-open-slot", "the slot reveal names an invalid open slot");
  refuse(typeof value.consensus_finality === "string", "reveal-finality", "the slot reveal must restate its finality position");

  if (value.state !== "revealed") {
    refuse(value.opening === null, "reveal-state", "a slot that is not revealed must publish no opening");
    refuse(value.slot_secret === null, "reveal-state", "a slot that is not revealed must publish no secret");
    return Object.freeze({ state: value.state, slot: value.slot, openSlot: value.open_slot, opening: null, slotSecret: null });
  }

  exactKeys(value.opening, ["statement", "curator_key", "signature"], "slot reveal opening");
  const statement = value.opening.statement;
  exactKeys(statement, ["schema", "authority_id", "mission_id", "slot", "commitment"], "slot reveal statement");
  refuse(statement.schema === STATEMENT_SCHEMA, "reveal-statement", "unsupported slot reveal statement schema");
  refuse(statement.authority_id === authorityId, "reveal-statement", "the slot reveal statement names another authority");
  refuse(Number.isSafeInteger(statement.mission_id) && statement.mission_id >= 0, "reveal-statement", "the slot reveal mission id is invalid");
  refuse(statement.slot === value.slot, "reveal-statement", "the slot reveal statement names a different slot than the document");
  refuse(typeof statement.commitment === "string" && HEX_32.test(statement.commitment), "reveal-statement", "the slot reveal commitment is invalid");
  refuse(typeof value.opening.curator_key === "string" && HEX_32.test(value.opening.curator_key), "reveal-curator", "the slot reveal curator key is invalid");
  refuse(typeof value.opening.signature === "string" && HEX_64.test(value.opening.signature), "reveal-signature", "the slot reveal signature is invalid");
  refuse(typeof value.slot_secret === "string" && HEX_32.test(value.slot_secret), "reveal-secret", "the published slot secret is invalid");

  return Object.freeze({
    state: "revealed",
    slot: value.slot,
    openSlot: value.open_slot,
    slotSecret: value.slot_secret,
    opening: Object.freeze({
      statement: Object.freeze({
        schema: statement.schema,
        authorityId: statement.authority_id,
        missionId: statement.mission_id,
        slot: statement.slot,
        commitment: statement.commitment,
      }),
      curatorKey: value.opening.curator_key,
      signature: value.opening.signature,
    }),
  });
}

function hexBytes(hex) {
  return Uint8Array.from(hex.match(/../g) ?? [], (pair) => Number.parseInt(pair, 16));
}

/**
 * **The part of the check a browser can honestly make.**
 *
 * Given a parsed reveal and the receipt retained before play, this decides
 * everything except the sponge. It NEVER returns a bare "ok": the success arm is
 * `state: "binding-holds"` and carries `spongeChecked: false`, so a caller cannot
 * render it as a completed verification. The remaining step — does
 * `commit(slot_secret, slot)` equal this commitment — needs Lean, and the result
 * names the command that runs it.
 *
 * Refusals, each by name:
 * * `not-revealed` — the node published no secret; nothing has been checked;
 * * `slot-mismatch` / `mission-mismatch` — the reveal is about a different run;
 * * `commitment-substituted` — ⚠ the reveal opens a commitment that is NOT the one
 *   you were shown before you played;
 * * `wrong-curator` / `bad-signature` — not signed by the pinned curator key.
 */
export async function checkRevealAgainstReceipt(reveal, receipt, curatorPublicKey) {
  const bad = (code, reason) => Object.freeze({ state: "refused", code, reason });

  if (!object(receipt) || !validReceipt(receipt)) {
    return bad("no-receipt", "You kept no verified opening for this slot, so there is nothing to check the reveal against. Only a copy retained BEFORE playing can establish the instance predates your session.");
  }
  if (!object(reveal) || reveal.state !== "revealed") {
    return bad("not-revealed", `The node published no secret for this slot (state: ${reveal?.state ?? "unknown"}). Nothing has been verified.`);
  }
  if (reveal.slot !== receipt.statement.slot) {
    return bad("slot-mismatch", `Your receipt is for slot ${receipt.statement.slot}; this reveal is for slot ${reveal.slot}.`);
  }
  if (reveal.opening.statement.missionId !== receipt.statement.mission_id) {
    return bad("mission-mismatch", `Your receipt is for mission ${receipt.statement.mission_id}; this reveal is for mission ${reveal.opening.statement.missionId}.`);
  }
  // ⚑ THE SUBSTITUTION CHECK — the one comparison that carries the ordering claim.
  if (reveal.opening.statement.commitment !== receipt.statement.commitment) {
    return bad(
      "commitment-substituted",
      "The reveal opens a DIFFERENT commitment than the one you were shown before you played. Your run was not judged against the instance you were promised.",
    );
  }
  if (typeof curatorPublicKey !== "string" || !HEX_32.test(curatorPublicKey)) {
    return bad("wrong-curator", "Checking a reveal needs the curator key this deployment is pinned to.");
  }
  if (receipt.curator_key !== curatorPublicKey || reveal.opening.curatorKey !== curatorPublicKey) {
    return bad("wrong-curator", "The reveal names a curator key that is not this deployment's pin.");
  }

  const subtle = globalThis.crypto?.subtle;
  if (!subtle) return bad("crypto-unavailable", "Web Crypto Ed25519 is required to check a slot reveal.");
  let key;
  try {
    key = await subtle.importKey("raw", hexBytes(curatorPublicKey), { name: "Ed25519" }, false, ["verify"]);
  } catch {
    return bad("crypto-unavailable", "The curator Ed25519 key could not be imported.");
  }
  // Re-derived from the STRUCTURED fields, as everywhere else: verifying against a
  // pre-encoded string the responder supplied would verify the responder's bytes.
  const message = new TextEncoder().encode(slotStatementMessage(reveal.opening.statement));
  const valid = await subtle.verify({ name: "Ed25519" }, key, hexBytes(reveal.opening.signature), message);
  if (!valid) return bad("bad-signature", "The reveal is not signed by the pinned curator key.");

  return Object.freeze({
    state: "binding-holds",
    slot: reveal.slot,
    commitment: receipt.statement.commitment,
    slotSecret: reveal.slotSecret,
    openSlot: reveal.openSlot,
    /**
     * ⚠ FALSE, always, and deliberately. The browser holds no Poseidon2-BabyBear
     * sponge: `HiddenInstance.commit` is authored in Lean and a JavaScript copy of
     * it would be an unproven second implementation, which is not a check.
     */
    spongeChecked: false,
    remaining:
      "Confirmed: this reveal opens the exact commitment you retained before playing, signed by the pinned curator. NOT yet confirmed: that the published secret actually opens that commitment — that is a Poseidon2 sponge authored in Lean, and this page has no copy of it. Run `dregg-node poa-verify-slot-reveal` with the two files to finish the check.",
  });
}

/**
 * The two files a player hands to `dregg-node poa-verify-slot-reveal`.
 *
 * Returned as text rather than triggering a download so the caller decides the
 * delivery. `reveal` is the RAW served document, not the parsed one: the verifier
 * parses it itself with `deny_unknown_fields`, and re-serialising a parse would
 * hand it this page's opinion of the bytes instead of the node's.
 */
export function exportVerificationBundle(receipt, rawRevealDocument) {
  refuse(validReceipt(receipt), "receipt-shape", "cannot export an invalid receipt");
  return Object.freeze({
    openingFileName: `poa-slot-${receipt.statement.slot}-opening.json`,
    openingJson: `${JSON.stringify(receipt, null, 2)}\n`,
    revealFileName: `poa-slot-${receipt.statement.slot}-reveal.json`,
    revealJson: `${JSON.stringify(rawRevealDocument, null, 2)}\n`,
    command:
      `dregg-node poa-verify-slot-reveal \\\n` +
      `  --curator-key ${receipt.curator_key} \\\n` +
      `  --opening poa-slot-${receipt.statement.slot}-opening.json \\\n` +
      `  --reveal poa-slot-${receipt.statement.slot}-reveal.json`,
  });
}

/**
 * Fetch the reveal for one slot. Never throws: every failure is a STATE, in the
 * same posture as `loadSlotState` — this can only fail toward "not verified",
 * never toward claiming a binding that was not checked.
 */
export async function loadSlotReveal({ authorityId, slot, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof authorityId !== "string" || !HEX_32.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "reveal-authority", reason: "This terminal does not know which network to ask" });
  }
  if (!Number.isSafeInteger(slot) || slot < 0) {
    return Object.freeze({ state: "unreachable", code: "reveal-slot", reason: "That is not a slot number" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "reveal-fetch", reason: "This browser gave the page no way to make a request" });
  }
  const url = new URL(
    `${prefix}/api/poa/signal/${authorityId}/slot/${slot}/reveal`,
    baseUrl ?? globalThis.location?.href ?? "https://invalid.local/",
  );
  let raw;
  let response;
  try {
    response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    raw = JSON.parse(await response.text());
  } catch {
    return Object.freeze({ state: "unreachable", code: "reveal-fetch", reason: "Nothing answered at this address" });
  }
  // ⚠ 409 and 404 carry a MEANINGFUL body — "still open", "unknown" — so they are
  // parsed rather than discarded as transport failures. Any other non-2xx is not.
  if (!response?.ok && response?.status !== 409 && response?.status !== 404) {
    return Object.freeze({ state: "unreachable", code: "reveal-status", reason: `The network answered HTTP ${response?.status ?? "nothing"}` });
  }
  let parsed;
  try {
    parsed = parseRevealDocument(raw, authorityId);
  } catch (error) {
    return Object.freeze({ state: "refused", code: error?.code ?? "reveal-shape", reason: error?.message ?? "the slot reveal was refused" });
  }
  return Object.freeze({ ...parsed, raw });
}
