import assert from "node:assert/strict";
import { test } from "node:test";
import {
  RECEIPTS_STORAGE_KEY,
  buildSlotOpeningReceipt,
  checkRevealAgainstReceipt,
  exportVerificationBundle,
  listSlotOpeningReceipts,
  loadSlotOpeningReceipt,
  loadSlotReveal,
  parseRevealDocument,
  retainSlotOpening,
} from "../src/slot-opening-receipt.js";
import { loadSlotState, slotStatementMessage } from "../src/today-board.js";

const AUTHORITY = "b".repeat(64);
const hex = (bytes) => [...bytes].map((byte) => byte.toString(16).padStart(2, "0")).join("");

/** A localStorage stand-in. Node has no DOM; this is the whole contract used. */
function fakeStorage(initial = {}) {
  const map = new Map(Object.entries(initial));
  return {
    getItem: (key) => (map.has(key) ? map.get(key) : null),
    setItem: (key, value) => { map.set(key, String(value)); },
    removeItem: (key) => { map.delete(key); },
    get size() { return map.size; },
  };
}

/** A real Ed25519 curator, and a real signature over the documented encoding. */
async function curator() {
  const pair = await crypto.subtle.generateKey({ name: "Ed25519" }, true, ["sign", "verify"]);
  const raw = new Uint8Array(await crypto.subtle.exportKey("raw", pair.publicKey));
  return {
    publicKeyHex: hex(raw),
    async sign(statement) {
      const message = new TextEncoder().encode(slotStatementMessage(statement));
      return hex(new Uint8Array(await crypto.subtle.sign({ name: "Ed25519" }, pair.privateKey, message)));
    },
  };
}

async function openingFor(who, { missionId = 1, slot = 42, commitment = "c".repeat(64) } = {}) {
  const statement = { schema: "POA-SLOT-OPENING-STATEMENT-1", authorityId: AUTHORITY, missionId, slot, commitment };
  return { statement, curatorKey: who.publicKeyHex, signature: await who.sign(statement) };
}

async function revealDocumentFor(who, { missionId = 1, slot = 42, commitment = "c".repeat(64), secret = "5c".repeat(32), openSlot = 43, state = "revealed" } = {}) {
  const statement = { schema: "POA-SLOT-OPENING-STATEMENT-1", authorityId: AUTHORITY, missionId, slot, commitment };
  return {
    format: "POA-SIGNAL-SLOT-REVEAL-1",
    authority_id: AUTHORITY,
    slot,
    state,
    open_slot: openSlot,
    opening: state === "revealed"
      ? {
        statement: { schema: statement.schema, authority_id: AUTHORITY, mission_id: missionId, slot, commitment },
        curator_key: who.publicKeyHex,
        signature: await who.sign(statement),
      }
      : null,
    slot_secret: state === "revealed" ? secret : null,
    consensus_finality: "not_asserted_by_this_view",
  };
}

// ───────────────────────────────────────────────────────────────────────────
// POLE ONE — the legitimate binding verifies.
// ───────────────────────────────────────────────────────────────────────────

test("a legitimate reveal binds to the opening retained before the session", async () => {
  const who = await curator();
  const storage = fakeStorage();
  const opening = await openingFor(who);

  const retention = retainSlotOpening(opening, { storage, recordedAt: "2026-08-09T00:00:00Z" });
  assert.equal(retention.state, "recorded");
  assert.equal(retention.receipt.schema, "POA-SLOT-OPENING-RECEIPT-1");
  assert.equal(retention.receipt.statement.commitment, "c".repeat(64));

  const reveal = parseRevealDocument(await revealDocumentFor(who), AUTHORITY);
  assert.equal(reveal.state, "revealed");

  const verdict = await checkRevealAgainstReceipt(reveal, retention.receipt, who.publicKeyHex);
  assert.equal(verdict.state, "binding-holds", verdict.reason ?? "");
  assert.equal(verdict.commitment, "c".repeat(64));
  assert.equal(verdict.slotSecret, "5c".repeat(32));
  // ⚠ The browser must NEVER claim the sponge step. It has no Poseidon2.
  assert.equal(verdict.spongeChecked, false);
  assert.match(verdict.remaining, /poa-verify-slot-reveal/);
});

test("the retained receipt survives a reload and is what the CLI consumes", async () => {
  const who = await curator();
  const storage = fakeStorage();
  const opening = await openingFor(who, { slot: 7 });
  retainSlotOpening(opening, { storage, recordedAt: "2026-08-09T00:00:00Z" });

  const reloaded = loadSlotOpeningReceipt(AUTHORITY, 7, storage);
  assert.ok(reloaded, "a retained receipt must be readable back");
  assert.equal(reloaded.statement.slot, 7);
  assert.equal(reloaded.curator_key, who.publicKeyHex);
  assert.equal(reloaded.signature.length, 128);

  const bundle = exportVerificationBundle(reloaded, await revealDocumentFor(who, { slot: 7 }));
  // The exported file must round-trip as the exact document shape.
  const parsedBack = JSON.parse(bundle.openingJson);
  assert.deepEqual(Object.keys(parsedBack).sort(), ["curator_key", "recorded_at", "schema", "signature", "statement"]);
  assert.deepEqual(Object.keys(parsedBack.statement).sort(), ["authority_id", "commitment", "mission_id", "schema", "slot"]);
  assert.match(bundle.command, /--curator-key/);
  assert.match(bundle.command, /--opening/);
  assert.match(bundle.command, /--reveal/);
});

// ───────────────────────────────────────────────────────────────────────────
// POLE TWO — a swapped commitment, a withheld secret, a forged curator.
// Each mutation asserted PRESENT before the verdict is read.
// ───────────────────────────────────────────────────────────────────────────

test("⚑ a reveal that opens a commitment you were not shown is REFUSED by name", async () => {
  const who = await curator();
  const storage = fakeStorage();

  const honest = await openingFor(who, { commitment: "c".repeat(64) });
  const retention = retainSlotOpening(honest, { storage, recordedAt: "2026-08-09T00:00:00Z" });

  // The hostile reveal is otherwise IMPECCABLE: really signed by the real
  // curator, internally consistent, correct slot and mission. Only the
  // commitment differs.
  const swapped = "d".repeat(64);
  assert.notEqual(swapped, retention.receipt.statement.commitment, "the mutation must actually change the commitment");
  const hostile = parseRevealDocument(await revealDocumentFor(who, { commitment: swapped }), AUTHORITY);
  assert.equal(hostile.opening.statement.commitment, swapped);

  // ...and it IS internally valid — against a receipt for the swapped value it
  // would pass — so the refusal below is about the substitution alone.
  const wouldPass = await checkRevealAgainstReceipt(
    hostile,
    buildSlotOpeningReceipt(await openingFor(who, { commitment: swapped }), "2026-08-09T00:00:00Z"),
    who.publicKeyHex,
  );
  assert.equal(wouldPass.state, "binding-holds", "the hostile reveal must be internally valid, or this test proves nothing");

  const verdict = await checkRevealAgainstReceipt(hostile, retention.receipt, who.publicKeyHex);
  assert.equal(verdict.state, "refused");
  assert.equal(verdict.code, "commitment-substituted");
});

test("⚑ a second, different opening for one slot is an EQUIVOCATION and never overwrites the first", async () => {
  const who = await curator();
  const storage = fakeStorage();

  const first = await openingFor(who, { commitment: "c".repeat(64) });
  const recorded = retainSlotOpening(first, { storage, recordedAt: "2026-08-09T00:00:00Z" });
  assert.equal(recorded.state, "recorded");

  const second = await openingFor(who, { commitment: "d".repeat(64) });
  assert.notEqual(second.statement.commitment, first.statement.commitment, "the mutation must actually change the commitment");

  const alarm = retainSlotOpening(second, { storage, recordedAt: "2026-08-09T01:00:00Z" });
  assert.equal(alarm.state, "equivocation");
  assert.equal(alarm.retained.statement.commitment, "c".repeat(64));
  assert.equal(alarm.served.statement.commitment, "d".repeat(64));

  // ⚑ THE LOAD-BEARING ASSERTION: the evidence was NOT replaced.
  const held = loadSlotOpeningReceipt(AUTHORITY, 42, storage);
  assert.equal(held.statement.commitment, "c".repeat(64), "the retained receipt is the evidence and must survive a second, different opening");
  assert.equal(listSlotOpeningReceipts(storage).length, 1);
});

test("⚑ loadSlotState REFUSES a node that equivocates about the open slot", async () => {
  const who = await curator();
  const storage = fakeStorage();
  const first = await openingFor(who, { commitment: "c".repeat(64) });
  retainSlotOpening(first, { storage, recordedAt: "2026-08-09T00:00:00Z" });

  const swapped = await openingFor(who, { commitment: "d".repeat(64) });
  assert.notEqual(swapped.statement.commitment, first.statement.commitment);
  const document = {
    format: "POA-SIGNAL-SLOT-1",
    authority_id: AUTHORITY,
    federation_id: AUTHORITY,
    open: true,
    opening: {
      statement: { schema: "POA-SLOT-OPENING-STATEMENT-1", authority_id: AUTHORITY, mission_id: 1, slot: 42, commitment: "d".repeat(64) },
      curator_key: swapped.curatorKey,
      signature: swapped.signature,
    },
    consensus_finality: "not-asserted",
  };
  const fetchImpl = async () => ({ ok: true, status: 200, text: async () => JSON.stringify(document) });

  const state = await loadSlotState({
    authorityId: AUTHORITY,
    curatorPublicKey: who.publicKeyHex,
    baseUrl: "https://poa.test/",
    fetchImpl,
    storage,
  });
  assert.equal(state.state, "refused", "a node serving a second commitment for one slot must not present as open");
  assert.equal(state.code, "slot-equivocation");
  assert.equal(state.retained.statement.commitment, "c".repeat(64));
});

test("⚑ a withheld secret is not a pass — still_open and unknown are REFUSED by name", async () => {
  const who = await curator();
  const receipt = buildSlotOpeningReceipt(await openingFor(who), "2026-08-09T00:00:00Z");

  for (const state of ["still_open", "unknown"]) {
    const parsed = parseRevealDocument(await revealDocumentFor(who, { state }), AUTHORITY);
    assert.equal(parsed.slotSecret, null, `a ${state} document must carry no secret`);
    const verdict = await checkRevealAgainstReceipt(parsed, receipt, who.publicKeyHex);
    assert.equal(verdict.state, "refused", state);
    assert.equal(verdict.code, "not-revealed", state);
  }
});

test("⚑ with no retained receipt there is nothing to verify, and it says so", async () => {
  const who = await curator();
  const reveal = parseRevealDocument(await revealDocumentFor(who), AUTHORITY);
  const verdict = await checkRevealAgainstReceipt(reveal, null, who.publicKeyHex);
  assert.equal(verdict.state, "refused");
  assert.equal(verdict.code, "no-receipt");
  assert.match(verdict.reason, /BEFORE playing/);
});

test("⚑ a ceremony minted under another curator key is REFUSED by name", async () => {
  const who = await curator();
  const impostor = await curator();
  assert.notEqual(impostor.publicKeyHex, who.publicKeyHex);

  const receipt = buildSlotOpeningReceipt(await openingFor(impostor), "2026-08-09T00:00:00Z");
  const reveal = parseRevealDocument(await revealDocumentFor(impostor), AUTHORITY);

  // Checked against the REAL pin, not the key the documents name.
  const verdict = await checkRevealAgainstReceipt(reveal, receipt, who.publicKeyHex);
  assert.equal(verdict.state, "refused");
  assert.equal(verdict.code, "wrong-curator");

  // ...and against the impostor's own key it would pass, which is exactly why
  // the pin must come from outside the documents.
  const unpinned = await checkRevealAgainstReceipt(reveal, receipt, impostor.publicKeyHex);
  assert.equal(unpinned.state, "binding-holds");
});

test("a reveal whose signature does not cover its statement is REFUSED", async () => {
  const who = await curator();
  const receipt = buildSlotOpeningReceipt(await openingFor(who), "2026-08-09T00:00:00Z");
  const document = await revealDocumentFor(who);

  const honest = document.opening.signature;
  document.opening.signature = "0".repeat(128);
  assert.notEqual(document.opening.signature, honest, "the mutation must actually change the signature");

  const reveal = parseRevealDocument(document, AUTHORITY);
  const verdict = await checkRevealAgainstReceipt(reveal, receipt, who.publicKeyHex);
  assert.equal(verdict.state, "refused");
  assert.equal(verdict.code, "bad-signature");
});

test("a reveal for another slot or mission is REFUSED by name", async () => {
  const who = await curator();
  const receipt = buildSlotOpeningReceipt(await openingFor(who, { slot: 42 }), "2026-08-09T00:00:00Z");

  const otherSlot = parseRevealDocument(await revealDocumentFor(who, { slot: 43, openSlot: 44 }), AUTHORITY);
  const bySlot = await checkRevealAgainstReceipt(otherSlot, receipt, who.publicKeyHex);
  assert.equal(bySlot.code, "slot-mismatch");

  const otherMission = parseRevealDocument(await revealDocumentFor(who, { missionId: 9 }), AUTHORITY);
  const byMission = await checkRevealAgainstReceipt(otherMission, receipt, who.publicKeyHex);
  assert.equal(byMission.code, "mission-mismatch");
});

// ───────────────────────────────────────────────────────────────────────────
// Document shape and transport.
// ───────────────────────────────────────────────────────────────────────────

test("a reveal document with an unknown or missing field is refused, never partially read", async () => {
  const who = await curator();
  const base = await revealDocumentFor(who);

  const extra = { ...base, surprise: 1 };
  assert.throws(() => parseRevealDocument(extra, AUTHORITY), /unknown or missing field/);

  const missing = { ...base };
  delete missing.open_slot;
  assert.throws(() => parseRevealDocument(missing, AUTHORITY), /unknown or missing field/);

  // A "revealed" document that carries no secret is a contradiction.
  const empty = { ...base, slot_secret: null };
  assert.throws(() => parseRevealDocument(empty, AUTHORITY), /slot secret is invalid/);

  // A non-revealed document that DOES carry one is the dangerous direction.
  const leaky = { ...base, state: "still_open", opening: null };
  assert.throws(() => parseRevealDocument(leaky, AUTHORITY), /must publish no secret/);

  // The honest document still parses, or the four refusals above pass for the
  // wrong reason.
  assert.equal(parseRevealDocument(base, AUTHORITY).state, "revealed");
});

test("loadSlotReveal reads the 409 and 404 bodies rather than discarding them", async () => {
  const who = await curator();

  const stillOpen = await revealDocumentFor(who, { state: "still_open", openSlot: 42 });
  const conflict = await loadSlotReveal({
    authorityId: AUTHORITY,
    slot: 42,
    baseUrl: "https://poa.test/",
    fetchImpl: async () => ({ ok: false, status: 409, text: async () => JSON.stringify(stillOpen) }),
  });
  assert.equal(conflict.state, "still_open", "a 409 carries the reason and must not be flattened to unreachable");
  assert.equal(conflict.openSlot, 42);

  const revealed = await revealDocumentFor(who);
  const ok = await loadSlotReveal({
    authorityId: AUTHORITY,
    slot: 42,
    baseUrl: "https://poa.test/",
    fetchImpl: async () => ({ ok: true, status: 200, text: async () => JSON.stringify(revealed) }),
  });
  assert.equal(ok.state, "revealed");
  // ⚠ The RAW document is carried through: the CLI parses the node's bytes, not
  // this page's re-serialisation of its own parse.
  assert.deepEqual(ok.raw, revealed);

  const broken = await loadSlotReveal({
    authorityId: AUTHORITY,
    slot: 42,
    baseUrl: "https://poa.test/",
    fetchImpl: async () => ({ ok: false, status: 500, text: async () => "{}" }),
  });
  assert.equal(broken.state, "unreachable");
});

test("storage that refuses to write still yields an exportable receipt", async () => {
  const who = await curator();
  const hostile = {
    getItem: () => null,
    setItem: () => { throw new Error("quota"); },
  };
  const retention = retainSlotOpening(await openingFor(who), { storage: hostile, recordedAt: "2026-08-09T00:00:00Z" });
  assert.equal(retention.state, "unstored");
  assert.ok(retention.receipt, "the player must still be able to download what could not be stored");
});

test("malformed retained records are dropped rather than repaired", async () => {
  const storage = fakeStorage({
    [RECEIPTS_STORAGE_KEY]: JSON.stringify({
      [`${AUTHORITY}:1`]: { schema: "POA-SLOT-OPENING-RECEIPT-1", nonsense: true },
      [`${AUTHORITY}:2`]: "not an object",
    }),
  });
  assert.equal(listSlotOpeningReceipts(storage).length, 0);
  assert.equal(loadSlotOpeningReceipt(AUTHORITY, 1, storage), null);
});
