import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  CUSTODY_BLOCKERS,
  FALLEN_WALLS,
  MAX_ROUNDS,
  NODE_BEHIND,
  NODE_SILENT,
  SESSION_SIGNER_METHOD,
  SIGNER_ABSENT,
  buildJudgedPanel,
  guessStatementMessage,
  judgedCustody,
  loadJudgedSession,
  mountJudgedPanel,
  openJudgedSession,
  openStatementMessage,
  parseSessionDocument,
  readingLabels,
  requestSessionSignature,
  routesReachableFrom,
  spendJudgedBurst,
} from "../src/judged-session.js";

class FakeElement {
  constructor(tagName) {
    this.tagName = tagName.toUpperCase();
    this.children = [];
    this.dataset = {};
    this.className = "";
    this.textContent = "";
    this.attributes = {};
  }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.children = [...nodes]; }
  setAttribute(name, value) { this.attributes[name] = value; }
}

function withFakeDocument(callback) {
  const previous = globalThis.document;
  globalThis.document = { createElement: (tag) => new FakeElement(tag) };
  try { return callback(); } finally { globalThis.document = previous; }
}

const AUTHORITY = "b".repeat(64);
const COMMITMENT = "c".repeat(64);
const PLAYER = "d".repeat(64);
const EXPECTED = { authorityId: AUTHORITY, commitment: COMMITMENT };

const code = (low, mid, high) => ({ low, mid, high });

function sessionDocument({ rounds = [], settlement = null, ...overrides } = {}) {
  const used = rounds.length;
  const solved = rounds.at(-1)?.exact === 3;
  return {
    format: "POA-SIGNAL-SESSION-1",
    judged: true,
    authority_id: AUTHORITY,
    mission_id: 1,
    slot: 42,
    slot_commitment: COMMITMENT,
    player_key: PLAYER,
    max_rounds: MAX_ROUNDS,
    rounds_used: used,
    rounds_remaining: MAX_ROUNDS - used,
    solved,
    open: !solved && used < MAX_ROUNDS,
    transcript: rounds,
    settlement,
    ...overrides,
  };
}

const openSlot = { state: "open", slot: 42, missionId: 1, commitment: COMMITMENT, consensusFinality: "not-asserted" };

const jsonFetch = (body, status = 200) => async () => ({
  ok: status >= 200 && status < 300,
  status,
  text: async () => JSON.stringify(body),
});

// ── The encodings, pinned against the node ────────────────────────────────────

test("the open statement is rebuilt in the node's documented field order", async () => {
  const message = openStatementMessage({ authorityId: AUTHORITY, slot: 42, playerKey: PLAYER });
  assert.equal(
    message,
    `{"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1","authority_id":"${AUTHORITY}","slot":42,"player_key":"${PLAYER}"}`,
  );
  // ⚠ TWO-SOURCE. The order is the node's. `open_statement_message` deliberately
  // is not served pre-encoded, so a client that re-encodes in any other order
  // signs bytes nobody asked for and is refused. Pinned against the Rust format
  // string AND its documented shape, not against this test's own expectation.
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(
    rust,
    /\{"schema":"\{schema\}","authority_id":"\{authority\}","slot":\{slot\},"player_key":"\{player\}"\}/,
  );
  assert.match(
    rust,
    /"schema":"POA-SIGNAL-SESSION-OPEN-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>"/,
  );
  assert.match(rust, /POA_SIGNAL_SESSION_OPEN_STATEMENT_V1: &str = "POA-SIGNAL-SESSION-OPEN-STATEMENT-1"/);
});

test("the guess statement carries the round, which is what makes a replay refuse", async () => {
  const message = guessStatementMessage({
    authorityId: AUTHORITY, slot: 42, playerKey: PLAYER, round: 2, guess: code(1, 4, 5),
  });
  assert.equal(
    message,
    `{"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1","authority_id":"${AUTHORITY}","slot":42,` +
    `"player_key":"${PLAYER}","round":2,"guess":{"low":1,"mid":4,"high":5}}`,
  );
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(
    rust,
    /"schema":"POA-SIGNAL-SESSION-GUESS-STATEMENT-1","authority_id":"<hex32>","slot":<n>,"player_key":"<hex32>","round":<n>,"guess":\{"low":n,"mid":n,"high":n\}/,
  );
  // The band order inside the guess object is load-bearing and easy to transpose.
  assert.match(rust, /"guess":\{\{"low":\{low\},"mid":\{mid\},"high":\{high\}\}\}/);
});

test("the burst budget and the document format are the node's, not this page's", async () => {
  const persist = await readFile(new URL("../../persist/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(persist, new RegExp(`POA_SIGNAL_SESSION_MAX_ROUNDS: usize = ${MAX_ROUNDS};`));
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(rust, /POA_SIGNAL_SESSION_FORMAT_V1: &str = "POA-SIGNAL-SESSION-1"/);
});

test("the session response fields are exactly the ones the node serves, in both directions", async () => {
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  const struct = rust.slice(rust.indexOf("pub struct PoaSignalSessionResponseV1"));
  const served = [...struct.slice(0, struct.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((match) => match[1]);
  // Every field the node serves must be one this parser knows, and every field
  // this parser demands must be one the node serves. A one-sided check lets a
  // new field arrive and be silently ignored, which is how a client stops
  // noticing that the thing it renders changed shape.
  const known = Object.keys(sessionDocument()).sort();
  assert.deepEqual(served.slice().sort(), known);
});

/**
 * ⚑ EXPECTED RED UNTIL THE NODE-SIDE TRANSCRIPT WORK IS COMMITTED.
 *
 * This client is built against a settlement that names the whole played
 * TRANSCRIPT, because that is what closes the blind path: a claim carrying only
 * a code is one the node did not watch anybody earn, and
 * `verify_claim_transcript_was_played` refuses it. That mechanism is real and is
 * in the shared working tree — it is NOT in `47cf23360` or `e1410b0f8`, and at
 * those commits `PoaSignalSessionSettlementV1` still has only `code` and
 * `verify_claim_transcript_was_played` does not exist at all.
 *
 * The client deliberately does NOT accept both shapes. Two shapes that agree
 * today are two shapes that disagree later, and the code-only one is the path
 * that was closed on purpose. So this pin reds against a tree where the node
 * half has not landed, and that red is the honest report of a real split —
 * not a flake to route around. It goes green when the sibling lands.
 */
test("the settlement names the played transcript, not just the solving code", async () => {
  const rust = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  const settlement = rust.slice(rust.indexOf("pub struct PoaSignalSessionSettlementV1"));
  const fields = [...settlement.slice(0, settlement.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((m) => m[1]);
  assert.deepEqual(
    fields.slice().sort(),
    ["claims_route", "code", "method", "mission_id", "note", "transcript"],
    "the node's settlement has no `transcript` field, so the node-side transcript work is not in this " +
    "tree. This client is built against the transcript-carrying settlement on purpose; see the docblock.",
  );
  const adapter = await readFile(new URL("../../node/src/poa_signal_adapter.rs", import.meta.url), "utf8");
  assert.match(adapter, /fn verify_claim_transcript_was_played/,
    "the gate that makes a session the only way to settle is absent from this tree");
});

// ── The document, checked field by field ──────────────────────────────────────

test("a session document is checked field by field and cannot carry an unknown one", () => {
  const parsed = parseSessionDocument(sessionDocument(), EXPECTED);
  assert.equal(parsed.judged, true);
  assert.equal(parsed.roundsRemaining, MAX_ROUNDS);
  assert.throws(
    () => parseSessionDocument({ ...sessionDocument(), extra: 1 }, EXPECTED),
    (error) => error.code === "session-field",
  );
  const { solved, ...missing } = sessionDocument();
  assert.throws(() => parseSessionDocument(missing, EXPECTED), (error) => error.code === "session-field");
});

test("a document that does not declare itself judged is REFUSED, never downgraded to practice", () => {
  assert.throws(
    () => parseSessionDocument(sessionDocument({ judged: false }), EXPECTED),
    (error) => error.code === "session-not-judged",
  );
});

test("a session played against another commitment is not the instance the curator signed", () => {
  assert.throws(
    () => parseSessionDocument(sessionDocument({ slot_commitment: "e".repeat(64) }), EXPECTED),
    (error) => error.code === "session-commitment",
  );
  assert.throws(
    () => parseSessionDocument(sessionDocument({ authority_id: "f".repeat(64) }), EXPECTED),
    (error) => error.code === "session-authority",
  );
});

test("reading a session at all requires a VERIFIED slot to compare against", () => {
  assert.throws(() => parseSessionDocument(sessionDocument(), {}), (error) => error.code === "session-expectation");
  assert.throws(
    () => parseSessionDocument(sessionDocument(), { authorityId: AUTHORITY, commitment: "short" }),
    (error) => error.code === "session-expectation",
  );
});

test("the accounting fields must agree with the transcript they summarize", () => {
  const rounds = [{ guess: code(0, 1, 2), exact: 1, present: 1 }];
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds, rounds_used: 3, rounds_remaining: 2 }), EXPECTED),
    (error) => error.code === "session-accounting",
  );
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds, rounds_remaining: 1 }), EXPECTED),
    (error) => error.code === "session-accounting",
  );
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds, solved: true }), EXPECTED),
    (error) => error.code === "session-accounting",
  );
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds, open: false }), EXPECTED),
    (error) => error.code === "session-accounting",
  );
});

test("a band outside 0..=5 is refused rather than wrapped, as the node refuses it", () => {
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds: [{ guess: code(0, 1, 6), exact: 0, present: 0 }] }), EXPECTED),
    (error) => error.code === "session-band",
  );
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds: [{ guess: code(0, 1, -1), exact: 0, present: 0 }] }), EXPECTED),
    (error) => error.code === "session-band",
  );
});

test("a classification naming more bands than a code has is refused", () => {
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds: [{ guess: code(0, 1, 2), exact: 2, present: 2 }] }), EXPECTED),
    (error) => error.code === "session-classification",
  );
});

test("an unsolved session may not carry a settlement, and a solved one must", () => {
  const rounds = [{ guess: code(0, 1, 2), exact: 1, present: 0 }];
  const settlement = {
    mission_id: 1, transcript: [code(0, 1, 2)], code: code(0, 1, 2),
    method: "poa-signal", claims_route: `/api/poa/signal/${AUTHORITY}/claims`, note: "staging only",
  };
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds, settlement }), EXPECTED),
    (error) => error.code === "session-settlement",
  );
  const solvedRounds = [{ guess: code(3, 3, 3), exact: 3, present: 0 }];
  assert.throws(
    () => parseSessionDocument(sessionDocument({ rounds: solvedRounds, settlement: null }), EXPECTED),
    (error) => error.code === "session-settlement",
  );
});

test("the settlement transcript must be the rounds actually played, not a second list", () => {
  const rounds = [
    { guess: code(0, 1, 2), exact: 1, present: 0 },
    { guess: code(3, 3, 3), exact: 3, present: 0 },
  ];
  const base = {
    mission_id: 1, method: "poa-signal",
    claims_route: `/api/poa/signal/${AUTHORITY}/claims`, note: "staging only",
  };
  // A settlement that drops a round: the claim would be refused as a length
  // mismatch by the node, with a message that reads like a judge failure.
  assert.throws(
    () => parseSessionDocument(sessionDocument({
      rounds, settlement: { ...base, transcript: [code(3, 3, 3)], code: code(3, 3, 3) },
    }), EXPECTED),
    (error) => error.code === "session-settlement",
  );
  // A settlement that rewrites a round it claims was played.
  assert.throws(
    () => parseSessionDocument(sessionDocument({
      rounds, settlement: { ...base, transcript: [code(5, 5, 5), code(3, 3, 3)], code: code(3, 3, 3) },
    }), EXPECTED),
    (error) => error.code === "session-settlement",
  );
  // A settling code that is not the last round.
  assert.throws(
    () => parseSessionDocument(sessionDocument({
      rounds, settlement: { ...base, transcript: [code(0, 1, 2), code(3, 3, 3)], code: code(0, 1, 2) },
    }), EXPECTED),
    (error) => error.code === "session-settlement",
  );
  const good = parseSessionDocument(sessionDocument({
    rounds, settlement: { ...base, transcript: [code(0, 1, 2), code(3, 3, 3)], code: code(3, 3, 3) },
  }), EXPECTED);
  assert.equal(good.settlement.transcript.length, 2);
  assert.equal(good.settlement.claimsRoute, `/api/poa/signal/${AUTHORITY}/claims`);
});

// ── LOCKED / DRIFT ────────────────────────────────────────────────────────────

test("a reading is rendered as LOCKED and DRIFT, in the spelling the rack already uses", async () => {
  assert.deepEqual({ ...readingLabels({ exact: 2, present: 1 }) }, { locked: "2 LOCKED", drift: "1 DRIFT" });
  const app = await readFile(new URL("../src/app.js", import.meta.url), "utf8");
  assert.match(app, /\$\{turn\.exact\} LOCKED/);
  assert.match(app, /\$\{turn\.present\} DRIFT/);
});

test("this module contains no classifier: LOCKED and DRIFT are read, never computed", async () => {
  const source = await readFile(new URL("../src/judged-session.js", import.meta.url), "utf8");
  // ⚠ The one rule that must never be re-implemented here. A client-side scorer
  // would be a second game, and the node's Lean classification is the only one
  // that settles.
  //
  // Comments AND string literals are stripped before looking, because this is a
  // check on CODE. The docblocks explain the target at length and the panel copy
  // tells a player their reading was "against the judged target" — which is the
  // fact they most need. Neither is a computation. What a classifier actually
  // needs is a BINDING holding the target, so that is what is looked for, and
  // `const target =` still reds this instantly.
  const code = source
    .replace(/\/\*[\s\S]*?\*\//g, "")
    .replace(/^\s*\/\/.*$/gm, "")
    .replace(/`(?:[^`\\]|\\.)*`/g, '""')
    .replace(/"(?:[^"\\]|\\.)*"/g, '""')
    .replace(/'(?:[^'\\]|\\.)*'/g, '""');
  assert.doesNotMatch(code, /\btarget\b/i, "a classifier would need a binding for the target");
  assert.doesNotMatch(code, /\bsecret\b/i, "a classifier would need the slot secret");
  assert.doesNotMatch(code, /\bseed\b/i, "a classifier would need the run seed");
  // `exact` and `present` may only ever be READ off a parsed document — never
  // accumulated, which is what scoring a guess looks like.
  assert.doesNotMatch(code, /exact\s*(\+\+|\+=)/);
  assert.doesNotMatch(code, /present\s*(\+\+|\+=)/);
  // And the practice runtime's own scorer must not have been imported here.
  assert.doesNotMatch(source, /from "\.\/(signal-runtime|hidden-instance)\.js"/);

  // ⚑ THE GUARD MUST BE ABLE TO GO RED. Stripping comments and strings is
  // exactly the kind of step that can quietly reduce to erasing the file, at
  // which point every `doesNotMatch` above passes vacuously forever. So: the
  // stripped text still has to contain the real code, and the same stripper run
  // over a planted classifier still has to catch it.
  assert.match(code, /export function parseSessionDocument/);
  assert.match(code, /exact \+ present <= 3/);
  const planted = "const target = drawTarget(secret, seed);\nif (guess.low === target.low) exact += 1;"
    .replace(/\/\*[\s\S]*?\*\//g, "")
    .replace(/^\s*\/\/.*$/gm, "")
    .replace(/`(?:[^`\\]|\\.)*`/g, '""')
    .replace(/"(?:[^"\\]|\\.)*"/g, '""')
    .replace(/'(?:[^'\\]|\\.)*'/g, '""');
  assert.match(planted, /\btarget\b/i);
  assert.match(planted, /\bsecret\b/i);
  assert.match(planted, /\bseed\b/i);
  assert.match(planted, /exact\s*(\+\+|\+=)/);
});

// ── Custody ───────────────────────────────────────────────────────────────────

test("custody detects the scoped signer, and says what still bites", () => {
  const none = judgedCustody(null);
  assert.equal(none.canPlay, false);
  assert.equal(none.identityAvailable, false);
  assert.equal(none.signerAvailable, false);
  assert.equal(none.blocker.code, SIGNER_ABSENT.code);

  // An extension that predates the scoped signer: identity but no signer.
  const oldExtension = judgedCustody({ getActiveIdentity: async () => ({}), signTurnV3: async () => ({}) });
  assert.equal(oldExtension.canPlay, false);
  assert.equal(oldExtension.identityAvailable, true);
  assert.equal(oldExtension.signerAvailable, false);
  assert.equal(oldExtension.blocker.code, "signer-not-installed");

  // ⚑ THE WALLS THAT FELL. With the signer installed and nothing measured, the
  // blocker is no longer "the code gates this" — it is `NODE_SILENT`, an honest
  // "nothing answered yet". The bearer wall is gone from the code entirely.
  const provider = {
    getActiveIdentity: async () => ({}),
    signTurnV3: async () => ({}),
    [SESSION_SIGNER_METHOD]: async () => ({}),
  };
  const withSigner = judgedCustody(provider);
  assert.equal(withSigner.signerAvailable, true);
  assert.equal(withSigner.blocker.code, NODE_SILENT.code);
  assert.equal(withSigner.canPlay, false, "nothing was measured yet, so canPlay stays false");
  assert.equal(withSigner.routesReachable, null);

  // ⚑ A 401 IS NOW A STALE NODE, NOT A WALL. The distinction is the whole point:
  // "the code gates this" and "this deployment still does" call for opposite
  // actions, and the second one is fixed by a redeploy.
  const stale = judgedCustody(provider, { state: "unauthenticated" });
  assert.equal(stale.blocker.code, NODE_BEHIND.code);
  assert.match(stale.blocker.needs, /redeployed/);
  assert.match(stale.blocker.detail, /public_routes/);

  // Reachability is MEASURED, never assumed, and canPlay follows the measurement.
  assert.equal(routesReachableFrom({ state: "unauthenticated" }), false);
  assert.equal(routesReachableFrom({ state: "ready" }), true);
  assert.equal(routesReachableFrom({ state: "none" }), true);
  assert.equal(routesReachableFrom({ state: "refused" }), true);
  assert.equal(routesReachableFrom({ state: "unreachable" }), null);
  assert.equal(routesReachableFrom(null), null);
  assert.equal(judgedCustody(provider, { state: "unauthenticated" }).canPlay, false);
  assert.equal(judgedCustody(provider, { state: "none" }).canPlay, true);
  assert.equal(judgedCustody(null, { state: "none" }).canPlay, false, "no signer is still no play");
});

test("each custody blocker is a checkable fact about the node", async () => {
  // ⚑ ONE WALL LEFT, AND IT IS ABOUT SETTLING. `session-routes-authenticated`
  // was here this morning; it is now in FALLEN_WALLS, by name, so a reader can
  // tell a wall that fell from one nobody ever noticed.
  assert.deepEqual(
    CUSTODY_BLOCKERS.map((blocker) => blocker.code),
    ["claim-carrier-unbuildable"],
  );
  assert.deepEqual(
    FALLEN_WALLS.map((wall) => wall.code),
    ["no-player-message-signer", "session-routes-authenticated"],
  );
  for (const wall of FALLEN_WALLS) {
    assert.ok(wall.was.length > 0 && wall.landed.length > 0, `${wall.code} must say what it was and what landed`);
    assert.equal(wall.fell, "2026-08-07");
  }
  for (const blocker of [...CUSTODY_BLOCKERS, SIGNER_ABSENT, NODE_BEHIND, NODE_SILENT]) {
    assert.ok(blocker.needs.length > 0, `${blocker.code} must name what would unblock it`);
  }
  // ⚠ BOTH DIRECTIONS, the discipline `today-board.js` uses for the crate routes:
  // if either of these stops being true, this test reds and the copy that tells
  // a player "you cannot play" has to be rewritten rather than left to rot into
  // a lie. Each assertion below is the exact fact the blocker asserts.

  // ⚑ 0. THE FALLEN WALL, asserted FALLEN — not deleted. `no-player-message-signer`
  // used to lead this list; the day it stops being true in the other direction
  // (the signer removed, or quietly widened into an oracle) this reds.
  const page = await readFile(new URL("../../extension/src/page.ts", import.meta.url), "utf8");
  const signer = await readFile(new URL("../../extension/src/signal-session.ts", import.meta.url), "utf8");
  assert.match(page, new RegExp(`${SESSION_SIGNER_METHOD}\\(params: SignalSessionRequest\\)`),
    "the scoped session signer left the page provider");
  // It is SCOPED, and these are the three things that make it so. A signing
  // oracle would break every one of them.
  assert.doesNotMatch(page, /\bsignMessage\b/, "an arbitrary-message signer appeared on the provider");
  assert.doesNotMatch(page, /\bsignBytes\b/);
  assert.match(signer, /kind must be one of/, "the kind allowlist left the signer");
  assert.match(signer, /SIGNAL_SESSION_SCHEMAS = Object\.freeze\(\{\s*open:[^}]*guess:/,
    "the schema allowlist is no longer exactly the two session statements");
  assert.match(signer, /THE PLAYER KEY IS NOT A PARAMETER/,
    "the statement's subject is no longer structurally the signer");
  // Identity disclosure is still identity-only.
  assert.match(page, /getActiveIdentity\(\): Promise<ActiveDreggIdentity>/);
  assert.match(page, /no secret key, mnemonic, holding\s+\*\s+receipt, wallet-provider object, or signing capability is returned/);

  // ⚑ 1. INVERTED 2026-08-07. This assertion used to read `sessionAt >
  // protectedAt` — "the session routes are behind the bearer layer" — and it was
  // the source fact `CUSTODY_BLOCKERS[0]` stood on. The routes moved into
  // `public_routes`, so it now asserts the OPPOSITE, in the same place, with the
  // same both-directions discipline: if they are ever mounted protected again,
  // this reds and the copy that tells a player "you can play" has to change back.
  const api = await readFile(new URL("../../node/src/api.rs", import.meta.url), "utf8");
  const publicAt = api.indexOf("let mut public_routes = Router::new()");
  const protectedAt = api.indexOf("let protected_routes = Router::new()");
  const sessionAt = api.indexOf(".merge(crate::poa_signal_session::routes())");
  const slotAt = api.indexOf("poa_signal_slot_api::routes()");
  assert.ok(publicAt > 0 && protectedAt > publicAt, "route blocks moved; re-anchor this test");
  assert.ok(
    sessionAt > publicAt && sessionAt < protectedAt,
    "the session routes are no longer PUBLIC — a browser holds no bearer, so this page cannot play",
  );
  assert.ok(slotAt > publicAt && slotAt < protectedAt, "the slot publication is no longer public");
  // The abuse budget that replaced the bearer is not optional: a public write
  // surface with no explicit budget is the thing the move must never become.
  const sessionRs = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.match(sessionRs, /struct SessionAdmission/, "the abuse budget left the session module");
  assert.match(sessionRs, /session-player-rate-limit/, "the per-player-key budget is gone");
  assert.match(sessionRs, /session-busy/, "the in-flight ceiling is gone");
  // And the ORDER: the per-key budget is charged only after verification. The
  // opposite order is a way to lock a player out of their own run with a public key.
  const verifyAt = sessionRs.indexOf("verify_player_signature(");
  const chargeAt = sessionRs.indexOf("admission.charge_player(player_key)");
  assert.ok(verifyAt > 0 && chargeAt > verifyAt, "the per-key budget must be charged AFTER the signature verifies");

  // ⚑ 2. CORRECTED 2026-08-07, AND THE CORRECTION IS THE FINDING. These two lines
  // used to read:
  //     assert.match(signal, /keys\.join\(","\) !== "code,missionId,schema"/);
  //     assert.doesNotMatch(signal, /transcript/);
  // Both are FALSE at HEAD. `extension/src/poa-signal.ts` was cut over to
  // `{schema, missionId, transcript}` in 86786886d and this file was not, so the
  // carrier wall's second reason had rotted into a lie AND this test was RED at
  // HEAD — a caller-committed/callee-not split, found while moving the session
  // routes, not caused by it.
  //
  // What is asserted now is only what is TRUE: there is no Signal prepare route,
  // so nothing hands this PAGE unsigned bytes. Whether the EXTENSION can settle
  // a judged run end to end is a live question owned by that cutover; if it can,
  // this wall belongs in FALLEN_WALLS.
  const galley = await readFile(new URL("../../node/src/poa_galley_api.rs", import.meta.url), "utf8");
  assert.match(galley, /GALLEY_API_PATH\}\/command/, "the Galley's prepare route is the shape Signal lacks");
  assert.doesNotMatch(sessionRs, /session\/prepare/);
  const slotApi = await readFile(new URL("../../node/src/poa_signal_slot_api.rs", import.meta.url), "utf8");
  assert.doesNotMatch(slotApi, /\/prepare/, "a Signal prepare route appeared — this wall may have fallen");
  // And the wall says so about itself, rather than repeating the dead reason.
  assert.match(CUSTODY_BLOCKERS[0].detail, /CORRECTED 2026-08-07/);
  assert.doesNotMatch(CUSTODY_BLOCKERS[0].detail, /takes exactly `\{schema, missionId, code\}`(?! with)/);
});

// ── Signing, now that there is a signer ───────────────────────────────────────

const SIGNER_PLAYER = "55".repeat(32);

/** A provider whose signer re-derives the statement the way the extension does. */
function fakeSigner({ playerKey = SIGNER_PLAYER, statementFor = null, throws = null } = {}) {
  return {
    getActiveIdentity: async () => ({ publicKeyHex: playerKey }),
    async [SESSION_SIGNER_METHOD](request) {
      if (throws) throw throws;
      const statement = statementFor
        ? statementFor(request, playerKey)
        : request.kind === "open"
          ? openStatementMessage({ authorityId: request.authorityId, slot: request.slot, playerKey })
          : guessStatementMessage({
            authorityId: request.authorityId, slot: request.slot, playerKey,
            round: request.round, guess: request.guess,
          });
      return { kind: request.kind, schema: "x", playerKeyHex: playerKey, statement, signatureHex: "ab".repeat(64) };
    },
  };
}

test("a signature is checked against this page's OWN derivation before it is used", async () => {
  const base = { provider: fakeSigner(), kind: "open", authorityId: AUTHORITY, slot: 9 };
  const signed = await requestSessionSignature(base);
  assert.equal(signed.state, "signed");
  assert.equal(signed.playerKey, SIGNER_PLAYER);
  assert.equal(signed.statement, openStatementMessage({ authorityId: AUTHORITY, slot: 9, playerKey: SIGNER_PLAYER }));
  assert.equal(signed.signature, "ab".repeat(64));

  // ⚑ THE DRIFT POLE. An extension that signed a DIFFERENT statement is refused
  // here rather than producing a 401 that reads like a node fault. The mutation
  // is asserted present before the verdict.
  const drifted = openStatementMessage({ authorityId: AUTHORITY, slot: 10, playerKey: SIGNER_PLAYER });
  assert.notEqual(drifted, signed.statement, "the drift mutation must actually change the statement");
  const mismatch = await requestSessionSignature({
    ...base, provider: fakeSigner({ statementFor: () => drifted }),
  });
  assert.equal(mismatch.state, "unsigned");
  assert.equal(mismatch.code, "session-statement-mismatch");

  // Every other way the signer can fail to hand back something usable.
  assert.equal((await requestSessionSignature({ ...base, provider: {} })).code, SIGNER_ABSENT.code);
  assert.equal((await requestSessionSignature({ ...base, kind: "transfer" })).code, "session-kind");
  assert.equal(
    (await requestSessionSignature({ ...base, provider: fakeSigner({ playerKey: "nope" }) })).code,
    "session-player",
  );
  const declined = Object.assign(new Error("User declined"), { code: "user-declined" });
  const decline = await requestSessionSignature({ ...base, provider: fakeSigner({ throws: declined }) });
  assert.equal(decline.state, "declined");
  assert.equal(decline.code, "user-declined");
});

test("a guess signature covers exactly this round, and the POST carries what it signed", async () => {
  const sent = [];
  const fetchImpl = async (url, init) => {
    sent.push({ url: String(url), body: JSON.parse(init.body), method: init.method });
    return { ok: true, status: 200, text: async () => JSON.stringify(sessionDocument({
      rounds: [{ guess: code(0, 1, 2), exact: 1, present: 1 }],
    })) };
  };
  const result = await spendJudgedBurst({
    provider: fakeSigner(), authorityId: AUTHORITY, commitment: COMMITMENT, slot: 9,
    round: 0, guess: { low: 0, mid: 1, high: 2 },
    baseUrl: "https://example.test/", fetchImpl, prefix: "/node",
  });
  assert.equal(result.state, "ready");
  assert.equal(sent.length, 1);
  assert.equal(sent[0].method, "POST");
  assert.match(sent[0].url, /\/session\/guess$/);
  assert.deepEqual(sent[0].body, {
    player_key: SIGNER_PLAYER, round: 0, guess: { low: 0, mid: 1, high: 2 }, signature: "ab".repeat(64),
  });
});

test("opening posts the signed open statement, and a 401 is the honest bearer wall", async () => {
  const sent = [];
  const okFetch = async (url, init) => {
    sent.push({ url: String(url), body: JSON.parse(init.body) });
    return { ok: true, status: 200, text: async () => JSON.stringify(sessionDocument()) };
  };
  const opened = await openJudgedSession({
    provider: fakeSigner(), authorityId: AUTHORITY, commitment: COMMITMENT, slot: 9,
    baseUrl: "https://example.test/", fetchImpl: okFetch,
  });
  assert.equal(opened.state, "ready");
  assert.match(sent[0].url, /\/session\/open$/);
  assert.deepEqual(sent[0].body, { player_key: SIGNER_PLAYER, signature: "ab".repeat(64) });

  // A node that predates the 2026-08-07 route move still 401s. That is a STALE
  // DEPLOYMENT, not a wall, and the state keeps its name so the copy can say so.
  const stale = await openJudgedSession({
    provider: fakeSigner(), authorityId: AUTHORITY, commitment: COMMITMENT, slot: 9,
    baseUrl: "https://example.test/", fetchImpl: async () => ({ ok: false, status: 401, text: async () => "" }),
  });
  assert.equal(stale.state, "unauthenticated");
  assert.equal(stale.code, NODE_BEHIND.code);
  assert.equal(stale.reason, NODE_BEHIND.what);

  // A NAMED node refusal keeps its name — a replayed burst is not an outage.
  const replayed = await spendJudgedBurst({
    provider: fakeSigner(), authorityId: AUTHORITY, commitment: COMMITMENT, slot: 9,
    round: 0, guess: { low: 0, mid: 0, high: 0 }, baseUrl: "https://example.test/",
    fetchImpl: async () => ({
      ok: false, status: 409,
      text: async () => JSON.stringify({ reason: "session-round-mismatch", detail: "one round per signature" }),
    }),
  });
  assert.equal(replayed.state, "refused");
  assert.equal(replayed.code, "session-round-mismatch");

  // Nothing is signed, let alone posted, without a signer.
  let touched = false;
  const noSigner = await openJudgedSession({
    provider: { getActiveIdentity: async () => ({}) }, authorityId: AUTHORITY, commitment: COMMITMENT, slot: 9,
    baseUrl: "https://example.test/", fetchImpl: async () => { touched = true; return { ok: true, status: 200, text: async () => "{}" }; },
  });
  assert.equal(noSigner.code, SIGNER_ABSENT.code);
  assert.equal(touched, false, "a missing signer must not reach the network");
});

// ── Loading ───────────────────────────────────────────────────────────────────

test("every way of not reading a session lands as a state, never as a judged board", async () => {
  const base = { authorityId: AUTHORITY, commitment: COMMITMENT, playerKey: PLAYER, baseUrl: "https://example.test/" };
  assert.equal((await loadJudgedSession({ ...base, authorityId: "nope" })).state, "unreachable");
  assert.equal((await loadJudgedSession({ ...base, playerKey: null })).state, "unbound");
  assert.equal((await loadJudgedSession({ ...base, fetchImpl: null })).state, "unreachable");
  assert.equal((await loadJudgedSession({ ...base, fetchImpl: jsonFetch({}, 401) })).state, "unauthenticated");
  assert.equal((await loadJudgedSession({ ...base, fetchImpl: jsonFetch({}, 404) })).state, "none");
  assert.equal((await loadJudgedSession({ ...base, fetchImpl: jsonFetch({}, 500) })).state, "unreachable");
  assert.equal((await loadJudgedSession({
    ...base, fetchImpl: async () => { throw new Error("offline"); },
  })).state, "unreachable");
  const refused = await loadJudgedSession({ ...base, fetchImpl: jsonFetch(sessionDocument({ judged: false })) });
  assert.equal(refused.state, "refused");
  assert.equal(refused.code, "session-not-judged");
  const ready = await loadJudgedSession({ ...base, fetchImpl: jsonFetch(sessionDocument()) });
  assert.equal(ready.state, "ready");
  assert.equal(ready.session.playerKey, PLAYER);
});

test("a 401 read-back is reported as a node behind this build, not as a wall", async () => {
  const state = await loadJudgedSession({
    authorityId: AUTHORITY, commitment: COMMITMENT, playerKey: PLAYER,
    baseUrl: "https://example.test/", fetchImpl: jsonFetch({}, 401),
  });
  assert.equal(state.code, NODE_BEHIND.code);
  assert.equal(state.reason, NODE_BEHIND.what);
  // ⚑ AND THE ORDINARY PATH IS SERVED. The read-back is public now, which is what
  // makes a lost response recoverable instead of a lost burst.
  const served = await loadJudgedSession({
    authorityId: AUTHORITY, commitment: COMMITMENT, playerKey: PLAYER,
    baseUrl: "https://example.test/", fetchImpl: jsonFetch(sessionDocument()),
  });
  assert.equal(served.state, "ready");
});

// ── The panel, in the four states a player can be in ──────────────────────────

test("no slot open: the panel says practice-only and offers nothing judged", () => {
  const panel = buildJudgedPanel({ slot: { state: "closed" }, custody: judgedCustody(null) });
  assert.equal(panel.state, "sealed");
  assert.equal(panel.headline, "No slot is open");
  assert.equal(panel.action.enabled, false);
  assert.match(panel.detail, /practice/);
  assert.match(panel.detail, /ordinary state, not a fault/);
});

test("a slot that did not verify never presents as playable", () => {
  const panel = buildJudgedPanel({ slot: { state: "refused", code: "slot-bad-signature" } });
  assert.equal(panel.state, "sealed");
  assert.equal(panel.action.enabled, false);
  assert.match(panel.detail, /would not accept it \(slot-bad-signature\)/);
});

test("slot open + unbound identity: the reason is the identity, not a fake capability", () => {
  const panel = buildJudgedPanel({ slot: openSlot, custody: judgedCustody(null) });
  assert.equal(panel.state, "unbound");
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, "identity-unbound");
  assert.match(panel.headline, /no identity is bound/i);
  assert.match(panel.detail, /per player/);
});

test("slot open + bound identity, no signer installed: the reason says so, and no key is invented", () => {
  const panel = buildJudgedPanel({
    slot: openSlot,
    custody: judgedCustody({ getActiveIdentity: async () => ({}) }),
  });
  assert.equal(panel.state, "unplayable");
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, "signer-not-installed");
  assert.match(panel.detail, /no cell, no funds/);
  assert.match(panel.action.reason, /Needs: /);
});

test("slot open + signer installed, node behind: the reason is the DEPLOYMENT, not a wall", () => {
  const panel = buildJudgedPanel({
    slot: openSlot,
    custody: judgedCustody(fakeSigner(), { state: "unauthenticated" }),
  });
  assert.equal(panel.state, "unplayable");
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, NODE_BEHIND.code);
  assert.doesNotMatch(panel.detail, /will not sign/, "a fallen wall must not be re-asserted as copy");
  // ⚑ The copy must not claim the platform gates this. It does not, since today.
  assert.doesNotMatch(panel.action.reason, /behind the node's bearer layer/);
  assert.match(panel.action.reason, /still gates/, "the sentence is about THIS node, not the code");
  assert.match(panel.action.reason, /redeployed/);
});

test("⚑ THE POSITIVE POLE: signer installed and the route answered, the action is LIVE", () => {
  const panel = buildJudgedPanel({
    slot: openSlot,
    custody: judgedCustody(fakeSigner(), { state: "none" }),
  });
  assert.equal(panel.state, "openable");
  assert.equal(panel.action.enabled, true, "every observable precondition is met; the button must work");
  assert.equal(panel.action.code, "session-open");
  assert.match(panel.headline, /you can play it/);
  assert.match(panel.detail, /moves no DREGG and authorizes no turn/);
});

test("a live session mid-guesses renders the node's readings and cannot spend a burst", () => {
  const session = {
    state: "ready",
    session: parseSessionDocument(sessionDocument({
      rounds: [
        { guess: code(0, 1, 2), exact: 1, present: 1 },
        { guess: code(3, 1, 4), exact: 2, present: 0 },
      ],
    }), EXPECTED),
  };
  const panel = buildJudgedPanel({ slot: openSlot, custody: judgedCustody({ getActiveIdentity: async () => ({}) }), session });
  assert.equal(panel.state, "playing");
  assert.equal(panel.headline, "3 bursts left");
  assert.deepEqual(panel.rounds.map((round) => round.locked), ["1 LOCKED", "2 LOCKED"]);
  assert.deepEqual(panel.rounds.map((round) => round.drift), ["1 DRIFT", "0 DRIFT"]);
  assert.deepEqual(panel.rounds.map((round) => round.code), ["0-1-2", "3-1-4"]);
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, "signer-not-installed");
  assert.match(panel.detail, /this page never scores a guess/);

  // With the signer installed and the route answering, the SAME transcript
  // offers a live burst — and the readings are still read, never computed.
  const live = buildJudgedPanel({ slot: openSlot, custody: judgedCustody(fakeSigner(), session), session });
  assert.equal(live.state, "playing");
  assert.equal(live.action.enabled, true);
  assert.equal(live.action.code, "session-guess");
  assert.deepEqual(live.rounds, panel.rounds, "enabling an action must not change what was served");
});

test("a spent, unsolved session says the run ended and nothing was spent on chain", () => {
  const rounds = Array.from({ length: MAX_ROUNDS }, () => ({ guess: code(0, 0, 0), exact: 0, present: 0 }));
  const session = { state: "ready", session: parseSessionDocument(sessionDocument({ rounds }), EXPECTED) };
  const panel = buildJudgedPanel({ slot: openSlot, custody: judgedCustody({ getActiveIdentity: async () => ({}) }), session });
  assert.equal(panel.state, "spent");
  assert.equal(panel.headline, "Out of bursts");
  assert.match(panel.detail, /Nothing was spent on chain/);
  assert.equal(panel.action.enabled, false);
});

test("a settled win shows the transcript a claim must carry, and says who can post it", () => {
  const rounds = [
    { guess: code(0, 1, 2), exact: 1, present: 1 },
    { guess: code(3, 3, 3), exact: 3, present: 0 },
  ];
  const session = {
    state: "ready",
    session: parseSessionDocument(sessionDocument({
      rounds,
      settlement: {
        mission_id: 1, transcript: [code(0, 1, 2), code(3, 3, 3)], code: code(3, 3, 3),
        method: "poa-signal", claims_route: `/api/poa/signal/${AUTHORITY}/claims`,
        note: "`accepted` is admission staging and settles nothing; latest_height is the number that bites.",
      },
    }), EXPECTED),
  };
  const panel = buildJudgedPanel({ slot: openSlot, custody: judgedCustody({ getActiveIdentity: async () => ({}) }), session });
  assert.equal(panel.state, "settled");
  assert.equal(panel.headline, "Solved in 2 bursts");
  assert.match(panel.detail, /3-3-3 came back 3 LOCKED/);
  assert.match(panel.detail, /settles the game it served/);
  // The note is restated: `accepted: true` is not a settlement.
  assert.match(panel.detail, /admission staging/);
  assert.equal(panel.action.label, "Submit this claim");
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, "claim-carrier-unbuildable");
  assert.match(panel.action.reason, /ML-DSA-65/);
  assert.equal(panel.settlement.transcript.length, 2);
});

test("a refused session document is shown as refused, never as a judged board", () => {
  const panel = buildJudgedPanel({
    slot: openSlot,
    custody: judgedCustody({ getActiveIdentity: async () => ({}) }),
    session: { state: "refused", code: "session-commitment", reason: "played against another commitment" },
  });
  assert.equal(panel.state, "sealed");
  assert.equal(panel.action.enabled, false);
  assert.match(panel.detail, /session-commitment/);
});

test("a state that cannot play ends in a DISABLED action carrying a reason and a code", () => {
  const custody = judgedCustody({ getActiveIdentity: async () => ({}) });
  const panels = [
    buildJudgedPanel({}),
    buildJudgedPanel({ slot: { state: "closed" }, custody }),
    buildJudgedPanel({ slot: { state: "unreachable", reason: "nothing answered" }, custody }),
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(null) }),
    buildJudgedPanel({ slot: openSlot, custody }),
    // Signer installed, bearer wall standing: still disabled, different reason.
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(fakeSigner(), { state: "unauthenticated" }) }),
  ];
  for (const panel of panels) {
    assert.equal(panel.action.enabled, false, `${panel.state} must not offer an enabled judged action`);
    assert.ok(panel.action.reason.length > 20, `${panel.state} must give an honest reason`);
    assert.ok(panel.action.code.length > 0, `${panel.state} must carry a machine code`);
    assert.ok(!/coming soon|not yet|todo/i.test(panel.action.reason), `${panel.state} must not say "coming soon"`);
  }
});

test("every reason names a fact, and no panel reason survives its own wall falling", () => {
  // ⚑ The copy that says "you cannot play" must never outlive the reason. The
  // signer wall FELL, so no panel may still cite it as the thing that bites.
  const everyPanel = [
    buildJudgedPanel({}),
    buildJudgedPanel({ slot: { state: "closed" }, custody: judgedCustody(null) }),
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(null) }),
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(fakeSigner(), { state: "unauthenticated" }) }),
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(fakeSigner(), { state: "none" }) }),
  ];
  for (const panel of everyPanel) {
    assert.doesNotMatch(
      `${panel.detail} ${panel.action.reason}`,
      /will not sign a session statement|no method on the provider produces one/,
      `${panel.state} still tells a player the extension cannot sign, which is no longer true`,
    );
    assert.notEqual(panel.action.code, "no-player-message-signer");
  }
});

test("the panel mounts with the reason as text, not only as a tooltip", () => {
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const panel = buildJudgedPanel({ slot: openSlot, custody: judgedCustody(null) });
    mountJudgedPanel(root, panel);
    const card = root.children[0];
    assert.equal(card.dataset.state, "unbound");
    const button = card.children.find((node) => node.tagName === "BUTTON");
    assert.equal(button.disabled, true);
    const reason = card.children.find((node) => node.className === "judged-panel__reason");
    assert.ok(reason.textContent.length > 20);
    assert.equal(button.attributes["aria-describedby"], reason.id);
  });
});

test("the panel renders one round element per played round", () => {
  withFakeDocument(() => {
    const root = new FakeElement("div");
    const session = {
      state: "ready",
      session: parseSessionDocument(sessionDocument({
        rounds: [{ guess: code(0, 1, 2), exact: 1, present: 1 }],
      }), EXPECTED),
    };
    mountJudgedPanel(root, buildJudgedPanel({
      slot: openSlot, custody: judgedCustody({ getActiveIdentity: async () => ({}) }), session,
    }));
    const list = root.children[0].children.find((node) => node.tagName === "OL");
    assert.equal(list.children.length, 1);
    assert.deepEqual(list.children[0].children.map((node) => node.textContent), ["0-1-2", "1 LOCKED", "1 DRIFT"]);
  });
});

test("mounting refuses a root that cannot hold children", () => {
  assert.throws(() => mountJudgedPanel(null, buildJudgedPanel({})), TypeError);
});
