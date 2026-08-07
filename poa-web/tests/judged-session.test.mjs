import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";
import {
  CUSTODY_BLOCKERS,
  MAX_ROUNDS,
  buildJudgedPanel,
  guessStatementMessage,
  judgedCustody,
  loadJudgedSession,
  mountJudgedPanel,
  openStatementMessage,
  parseSessionDocument,
  readingLabels,
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
  const settlement = rust.slice(rust.indexOf("pub struct PoaSignalSessionSettlementV1"));
  const settlementFields = [...settlement.slice(0, settlement.indexOf("\n}")).matchAll(/pub (\w+):/g)].map((m) => m[1]);
  assert.deepEqual(settlementFields.slice().sort(),
    ["claims_route", "code", "method", "mission_id", "note", "transcript"]);
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

test("custody reports that this page cannot sign a session statement, and why", () => {
  const none = judgedCustody(null);
  assert.equal(none.canPlay, false);
  assert.equal(none.identityAvailable, false);
  const withIdentity = judgedCustody({ getActiveIdentity: async () => ({}), signTurnV3: async () => ({}) });
  assert.equal(withIdentity.canPlay, false);
  assert.equal(withIdentity.identityAvailable, true);
  assert.equal(withIdentity.blocker.code, "no-player-message-signer");
});

test("each custody blocker is a checkable fact about the node or the extension", async () => {
  assert.deepEqual(
    CUSTODY_BLOCKERS.map((blocker) => blocker.code),
    ["no-player-message-signer", "session-routes-authenticated", "claim-carrier-unbuildable"],
  );
  for (const blocker of CUSTODY_BLOCKERS) {
    assert.ok(blocker.needs.length > 0, `${blocker.code} must name what would unblock it`);
  }
  // ⚠ BOTH DIRECTIONS, the discipline `today-board.js` uses for the crate routes:
  // if any of these three stops being true, this test reds and the copy that
  // tells a player "you cannot play" has to be rewritten rather than left to rot
  // into a lie. Each assertion below is the exact fact the blocker asserts.

  // 1. The extension exposes no arbitrary-message signer for the player key.
  const page = await readFile(new URL("../../extension/src/page.ts", import.meta.url), "utf8");
  assert.doesNotMatch(page, /\bsignMessage\b/);
  assert.doesNotMatch(page, /\bsignBytes\b/);
  assert.match(page, /getActiveIdentity\(\): Promise<ActiveDreggIdentity>/);
  assert.match(page, /no secret key, mnemonic, holding\s+\*\s+receipt, wallet-provider object, or signing capability is returned/);

  // 2. The session routes are protected and the slot publication is not.
  const api = await readFile(new URL("../../node/src/api.rs", import.meta.url), "utf8");
  const publicAt = api.indexOf("let mut public_routes = Router::new()");
  const protectedAt = api.indexOf("let protected_routes = Router::new()");
  const sessionAt = api.indexOf("poa_signal_session::routes()");
  const slotAt = api.indexOf("poa_signal_slot_api::routes()");
  assert.ok(publicAt > 0 && protectedAt > publicAt, "route blocks moved; re-anchor this test");
  assert.ok(sessionAt > protectedAt, "the session routes are no longer protected — this page may now read them");
  assert.ok(slotAt > publicAt && slotAt < protectedAt, "the slot publication is no longer public");

  // 3. No Signal prepare route, and the one extension claim path carries no transcript.
  const signal = await readFile(new URL("../../extension/src/poa-signal.ts", import.meta.url), "utf8");
  assert.match(signal, /keys\.join\(","\) !== "code,missionId,schema"/);
  assert.doesNotMatch(signal, /transcript/);
  const galley = await readFile(new URL("../../node/src/poa_galley_api.rs", import.meta.url), "utf8");
  assert.match(galley, /GALLEY_API_PATH\}\/command/);
  const session = await readFile(new URL("../../node/src/poa_signal_session.rs", import.meta.url), "utf8");
  assert.doesNotMatch(session, /session\/prepare/);
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

test("this deployment's authenticated route is the honest 401 path", async () => {
  const state = await loadJudgedSession({
    authorityId: AUTHORITY, commitment: COMMITMENT, playerKey: PLAYER,
    baseUrl: "https://example.test/", fetchImpl: jsonFetch({}, 401),
  });
  assert.equal(state.code, "session-routes-authenticated");
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

test("slot open + bound identity: the reason names the missing signer, and no key is invented", () => {
  const panel = buildJudgedPanel({
    slot: openSlot,
    custody: judgedCustody({ getActiveIdentity: async () => ({}) }),
  });
  assert.equal(panel.state, "unplayable");
  assert.equal(panel.action.enabled, false);
  assert.equal(panel.action.code, "no-player-message-signer");
  assert.match(panel.detail, /no cell, no funds/);
  assert.match(panel.action.reason, /Needs: /);
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
  assert.equal(panel.action.code, "no-player-message-signer");
  assert.match(panel.detail, /this page never scores a guess/);
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

test("every panel state ends in a disabled action carrying a reason and a code", () => {
  const custody = judgedCustody({ getActiveIdentity: async () => ({}) });
  const panels = [
    buildJudgedPanel({}),
    buildJudgedPanel({ slot: { state: "closed" }, custody }),
    buildJudgedPanel({ slot: { state: "unreachable", reason: "nothing answered" }, custody }),
    buildJudgedPanel({ slot: openSlot, custody: judgedCustody(null) }),
    buildJudgedPanel({ slot: openSlot, custody }),
  ];
  for (const panel of panels) {
    assert.equal(panel.action.enabled, false, `${panel.state} must not offer an enabled judged action`);
    assert.ok(panel.action.reason.length > 20, `${panel.state} must give an honest reason`);
    assert.ok(panel.action.code.length > 0, `${panel.state} must carry a machine code`);
    assert.ok(!/coming soon|not yet|todo/i.test(panel.action.reason), `${panel.state} must not say "coming soon"`);
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
