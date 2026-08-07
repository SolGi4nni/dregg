import { ArtifactRefusal } from "./poag1.js";

/**
 * THE JUDGED SESSION — reading the deduction game the node actually scores, and
 * saying plainly which parts of it this browser can and cannot reach.
 *
 * A judged run is not a practice run with a flag set. It is a document served by
 * `node/src/poa_signal_session.rs` against a curator-committed slot, whose
 * LOCKED/DRIFT numbers came out of the Lean feedback oracle, and it is the only
 * kind that can settle. Practice is drawn client-side from
 * `HiddenInstance.practiceRunSeed`, has no session on any node, and settles
 * nothing. This module exists so those two can never be mistaken for one another
 * in the page: a document reaches `renderable` only if it says `judged: true`
 * AND its `slot_commitment` equals the commitment of the curator signature this
 * terminal already verified for itself.
 *
 * ⚠ THIS MODULE NEVER CLASSIFIES A GUESS. `exact` and `present` are read off the
 * wire and rendered. There is no scoring function here, not even to "preview" a
 * guess before sending it — a second implementation of the rule is a second rule,
 * and the whole point of a judged session is that the node's Lean classification
 * is the only one. The browser authors identity and intent; nothing else.
 *
 * ⚠ AND IT CANNOT PLAY, TODAY. Three separate things are missing, all of them in
 * the node/extension and none of them here; [`judgedCustody`] names whichever one
 * bites first and the panel renders the action DISABLED rather than inventing a
 * way around it. See `CUSTODY_BLOCKERS`.
 */

const SESSION_FORMAT = "POA-SIGNAL-SESSION-1";
const OPEN_STATEMENT_SCHEMA = "POA-SIGNAL-SESSION-OPEN-STATEMENT-1";
const GUESS_STATEMENT_SCHEMA = "POA-SIGNAL-SESSION-GUESS-STATEMENT-1";
const SIGNAL_CLAIM_METHOD = "poa-signal";

/** `POA_SIGNAL_SESSION_MAX_ROUNDS` in `persist/src/poa_signal_session.rs`. */
export const MAX_ROUNDS = 5;

/** A band is `0..=5`; the node refuses a wrapped one rather than reducing it. */
const MAX_BAND = 5;

const HEX_32 = /^[0-9a-f]{64}$/;

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, expected, at) {
  refuse(object(value), "session-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    "session-field",
    `${at} has an unknown or missing field; the exact set is: ${wanted.join(", ")}`,
  );
}

function band(value, at) {
  refuse(
    Number.isSafeInteger(value) && value >= 0 && value <= MAX_BAND,
    "session-band",
    `${at} must be an integer band from 0 through ${MAX_BAND}`,
  );
  return value;
}

function count(value, at, limit) {
  refuse(
    Number.isSafeInteger(value) && value >= 0 && value <= limit,
    "session-count",
    `${at} must be an integer from 0 through ${limit}`,
  );
  return value;
}

/**
 * The exact bytes a player signs to OPEN a judged session.
 *
 * ⚠ One template, in the node's field order, never `JSON.stringify` of anything
 * that arrived — the same rule `today-board.js` follows for the curator's slot
 * opening, and for the same reason: re-serialising a received object signs
 * whatever order and whatever extra keys the sender chose. Pinned against
 * `open_statement_message` in `node/src/poa_signal_session.rs` by
 * `tests/judged-session.test.mjs`.
 */
export function openStatementMessage({ authorityId, slot, playerKey }) {
  return `{"schema":"${OPEN_STATEMENT_SCHEMA}","authority_id":"${authorityId}",` +
    `"slot":${slot},"player_key":"${playerKey}"}`;
}

/**
 * The exact bytes a player signs to spend ONE burst.
 *
 * `round` is the number of bursts ALREADY spent. It is inside the signature, which
 * is why no session token exists and why a captured request replays into a refusal
 * rather than into a second burst.
 */
export function guessStatementMessage({ authorityId, slot, playerKey, round, guess }) {
  return `{"schema":"${GUESS_STATEMENT_SCHEMA}","authority_id":"${authorityId}",` +
    `"slot":${slot},"player_key":"${playerKey}","round":${round},` +
    `"guess":{"low":${guess.low},"mid":${guess.mid},"high":${guess.high}}}`;
}

function parseCode(value, at) {
  exactKeys(value, ["low", "mid", "high"], at);
  return Object.freeze({
    low: band(value.low, `${at} low band`),
    mid: band(value.mid, `${at} mid band`),
    high: band(value.high, `${at} high band`),
  });
}

function parseRound(value, at) {
  exactKeys(value, ["guess", "exact", "present"], at);
  const exact = count(value.exact, `${at} exact`, 3);
  const present = count(value.present, `${at} present`, 3);
  // The node's own bound: a code has three bands, so LOCKED and DRIFT together
  // can never name more than three of them. This is a SHAPE check on a served
  // number, not a re-derivation of the rule that produced it.
  refuse(exact + present <= 3, "session-classification",
    `${at} reports more classified bands than a three-band code has`);
  return Object.freeze({ guess: parseCode(value.guess, `${at} guess`), exact, present });
}

function parseSettlement(value, missionId, transcript) {
  exactKeys(value, ["mission_id", "transcript", "code", "method", "claims_route", "note"], "settlement");
  refuse(value.mission_id === missionId, "session-settlement",
    "the settlement names a different mission than the session it closes");
  refuse(value.method === SIGNAL_CLAIM_METHOD, "session-settlement",
    `the settlement names an unsupported claim method: ${value.method}`);
  refuse(typeof value.claims_route === "string" && value.claims_route.startsWith("/api/poa/signal/"),
    "session-settlement", "the settlement does not name a PoA Signal claims route");
  refuse(typeof value.note === "string" && value.note.length > 0, "session-settlement",
    "the settlement must restate what settling actually requires");
  refuse(Array.isArray(value.transcript), "session-settlement", "the settlement transcript must be a list");
  const settled = value.transcript.map((round, index) => parseCode(round, `settlement round ${index + 1}`));
  // ⚑ THE CLAIM IS MADE OF THIS, so it must be the transcript the player just
  // played and not a second list that happens to end the same way. The node
  // compares a submitted claim against its own stored rounds
  // (`verify_claim_transcript_was_played`); a client that showed one list and
  // submitted another would produce a refusal that reads like a judge failure.
  refuse(settled.length === transcript.length, "session-settlement",
    "the settlement transcript is a different length than the rounds actually played");
  settled.forEach((code, index) => {
    const played = transcript[index].guess;
    refuse(code.low === played.low && code.mid === played.mid && code.high === played.high,
      "session-settlement", `settlement round ${index + 1} is not the round that was played`);
  });
  const code = parseCode(value.code, "settlement code");
  const last = settled.at(-1);
  refuse(last && code.low === last.low && code.mid === last.mid && code.high === last.high,
    "session-settlement", "the settling code is not the last round of the transcript");
  return Object.freeze({
    missionId: value.mission_id,
    transcript: Object.freeze(settled),
    code,
    method: value.method,
    claimsRoute: value.claims_route,
    note: value.note,
  });
}

/**
 * Parse a served session document against the slot this terminal VERIFIED.
 *
 * `expected` carries the authority id and the commitment out of the curator
 * signature `today-board.js` already checked. Both are compared here, and that
 * comparison is the entire difference between a judged board and a practice one:
 * a document that is not `judged`, or that is played against some other
 * commitment, is REFUSED rather than downgraded to practice — because a practice
 * board wearing judged furniture is the confusion this whole module exists to
 * prevent.
 */
export function parseSessionDocument(value, expected) {
  refuse(object(expected) && HEX_32.test(expected.authorityId ?? "") && HEX_32.test(expected.commitment ?? ""),
    "session-expectation",
    "reading a judged session needs the authority and commitment of a VERIFIED slot opening");
  exactKeys(value, [
    "format", "judged", "authority_id", "mission_id", "slot", "slot_commitment",
    "player_key", "max_rounds", "rounds_used", "rounds_remaining", "solved", "open",
    "transcript", "settlement",
  ], "session document");
  refuse(value.format === SESSION_FORMAT, "session-format",
    `unsupported session document format: ${value.format}`);
  refuse(value.judged === true, "session-not-judged",
    "the served session does not declare itself judged; nothing here may be shown as a judged run");
  refuse(value.authority_id === expected.authorityId, "session-authority",
    "the served session belongs to another authority");
  refuse(value.slot_commitment === expected.commitment, "session-commitment",
    "the served session was played against a commitment this terminal did not verify, so it is " +
    "not the judged instance the curator signed");
  refuse(Number.isSafeInteger(value.slot) && value.slot >= 0, "session-slot", "the session slot is invalid");
  refuse(Number.isSafeInteger(value.mission_id) && value.mission_id >= 0, "session-mission",
    "the session mission id is invalid");
  refuse(typeof value.player_key === "string" && HEX_32.test(value.player_key), "session-player",
    "the session player key is invalid");
  refuse(value.max_rounds === MAX_ROUNDS, "session-budget",
    `the node reports a burst budget of ${value.max_rounds}; this terminal is built against ${MAX_ROUNDS}`);
  refuse(typeof value.solved === "boolean", "session-solved", "`solved` must be a boolean");
  refuse(typeof value.open === "boolean", "session-open", "`open` must be a boolean");
  refuse(Array.isArray(value.transcript), "session-transcript", "the transcript must be a list");
  refuse(value.transcript.length <= MAX_ROUNDS, "session-transcript",
    "the transcript reports more rounds than the budget allows");
  const transcript = value.transcript.map((round, index) => parseRound(round, `round ${index + 1}`));
  const roundsUsed = count(value.rounds_used, "rounds_used", MAX_ROUNDS);
  const roundsRemaining = count(value.rounds_remaining, "rounds_remaining", MAX_ROUNDS);
  refuse(roundsUsed === transcript.length, "session-accounting",
    "`rounds_used` disagrees with the transcript it is supposed to summarize");
  refuse(roundsUsed + roundsRemaining === MAX_ROUNDS, "session-accounting",
    "`rounds_used` and `rounds_remaining` do not account for the whole budget");
  const solvedByTranscript = transcript.at(-1)?.exact === 3;
  refuse(value.solved === solvedByTranscript, "session-accounting",
    "`solved` disagrees with the last round it is supposed to summarize");
  refuse(value.open === (!value.solved && roundsUsed < MAX_ROUNDS), "session-accounting",
    "`open` disagrees with the budget and the solved bit");
  // BOTH directions. The first version of this pair said `solved || settlement
  // === null` twice over, which passes a solved session carrying no settlement —
  // exactly the case the second line was written to catch.
  refuse(value.solved || value.settlement === null, "session-settlement",
    "an unsolved session carries a settlement, which would be a code the player never earned");
  refuse(!value.solved || value.settlement !== null, "session-settlement",
    "a solved session must name what to do next, and this one carries no settlement");
  return Object.freeze({
    judged: true,
    authorityId: value.authority_id,
    missionId: value.mission_id,
    slot: value.slot,
    slotCommitment: value.slot_commitment,
    playerKey: value.player_key,
    maxRounds: value.max_rounds,
    roundsUsed,
    roundsRemaining,
    solved: value.solved,
    open: value.open,
    transcript: Object.freeze(transcript),
    settlement: value.settlement === null ? null : parseSettlement(value.settlement, value.mission_id, transcript),
  });
}

/**
 * ⚑ WHY THIS BROWSER CANNOT PLAY A JUDGED SESSION, in the order the attempt hits
 * them. Each entry is a fact about the node or the extension, measured 2026-08-07,
 * NOT a policy choice made here — and each names the thing that would have to land
 * for the surface below to light up unchanged.
 *
 * None of these is worked around. Generating a keypair in page memory to sign the
 * open statement would be a player key with no cell, no funds and no ML-DSA half,
 * i.e. inventing custody to make a button clickable.
 */
export const CUSTODY_BLOCKERS = Object.freeze([
  Object.freeze({
    code: "no-player-message-signer",
    what: "The extension holds the player key but will not sign a session statement with it.",
    detail:
      "`window.dregg` exposes `getActiveIdentity()`, which returns a public key and explicitly no " +
      "signing capability, and `signTurnV3(turnBytes)`, which signs a decoded v3 Turn rather than " +
      "caller-chosen bytes. Opening a session needs a raw Ed25519 signature over " +
      "`open_statement_message`, and no method on the provider produces one.",
    needs: "a player-key signer for this documented statement, scoped to it — deliberately not a signing oracle",
  }),
  Object.freeze({
    code: "session-routes-authenticated",
    what: "The three session routes are behind the node's bearer layer; this page carries no bearer.",
    detail:
      "`poa_signal_session::routes()` is merged into `protected_routes` in `node/src/api.rs`, unlike " +
      "the slot publication, which is public and which this terminal does read and verify. Even the " +
      "read-back `GET …/session/{player}` is authenticated, so a transcript cannot be recovered here.",
    needs: "a public, player-signed read-back, or a bearer this origin is entitled to hold",
  }),
  Object.freeze({
    code: "claim-carrier-unbuildable",
    what: "The settling carrier cannot be built in a browser, and the one extension path that could submit is the closed blind one.",
    detail:
      "A claim is a postcard-encoded `SignedTurn` whose action authorization is a HYBRID Ed25519 + " +
      "ML-DSA-65 signature over the federation-bound message, priced against its own post-signing " +
      "shape. There is no `prepare` route for Signal the way `poa_galley_api` has `/command`, so " +
      "nothing hands this page unsigned bytes to pass to `signTurnV3`. And " +
      "`dregg.submitPoaSignalClaim` takes exactly `{schema, missionId, code}` with no transcript, " +
      "which `verify_claim_transcript_was_played` now refuses as `poa-signal-transcript-no-session`.",
    needs: "a node-side Signal prepare route returning unsigned postcard bytes, as the Galley already has",
  }),
]);

/**
 * What custody this page actually has for judged play.
 *
 * Never throws and never invents: it reports the FIRST blocker that bites, so the
 * panel's honest reason is the one a player would hit first rather than a list.
 */
export function judgedCustody(provider = globalThis.window?.dregg ?? null) {
  const identity = provider && typeof provider.getActiveIdentity === "function";
  return Object.freeze({
    canPlay: false,
    // Recorded because it is the honest half: the page CAN learn who the player
    // is, which is why the blocker is signing and not identity.
    identityAvailable: Boolean(identity),
    blocker: CUSTODY_BLOCKERS[0],
    blockers: CUSTODY_BLOCKERS,
  });
}

/**
 * Read a judged session back for one player.
 *
 * Never throws: every failure is a STATE, the discipline `loadSlotState` follows.
 * On this deployment the authenticated route answers 401 and that lands as
 * `unreachable`, which is the safe direction — this can only ever fail toward
 * "no judged session shown", never toward showing a practice board as judged.
 */
export async function loadJudgedSession({
  authorityId, commitment, playerKey, baseUrl,
  fetchImpl = globalThis.fetch, prefix = "/node",
} = {}) {
  if (typeof authorityId !== "string" || !HEX_32.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "session-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof playerKey !== "string" || !HEX_32.test(playerKey)) {
    return Object.freeze({ state: "unbound", code: "session-player", reason: "No player identity is bound to this terminal" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "session-fetch", reason: "No fetch is available in this environment" });
  }
  const url = new URL(
    `${prefix}/api/poa/signal/${authorityId}/session/${playerKey}`,
    baseUrl ?? globalThis.location?.href ?? "https://invalid.local/",
  );
  let document;
  try {
    const response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    if (response?.status === 401 || response?.status === 403) {
      return Object.freeze({
        state: "unauthenticated",
        code: "session-routes-authenticated",
        reason: "The session routes are authenticated and this page holds no bearer",
      });
    }
    if (response?.status === 404) {
      return Object.freeze({ state: "none", code: "session-not-open", reason: "No judged session has been opened for this player" });
    }
    if (!response?.ok) {
      return Object.freeze({ state: "unreachable", code: "session-status", reason: `The authority answered HTTP ${response?.status ?? "nothing"}` });
    }
    document = JSON.parse(await response.text());
  } catch {
    return Object.freeze({ state: "unreachable", code: "session-fetch", reason: "No PoA authority answered on this origin" });
  }
  try {
    return Object.freeze({ state: "ready", session: parseSessionDocument(document, { authorityId, commitment }) });
  } catch (error) {
    return Object.freeze({
      state: "refused",
      code: error?.code ?? "session-shape",
      reason: error?.message ?? "the session document was refused",
    });
  }
}

/** `${exact} LOCKED` / `${present} DRIFT`, the spelling `app.js` already uses. */
export function readingLabels(round) {
  return Object.freeze({ locked: `${round.exact} LOCKED`, drift: `${round.present} DRIFT` });
}

function codeText(code) {
  return `${code.low}-${code.mid}-${code.high}`;
}

/**
 * The judged panel: one state, one honest sentence about what a player may do.
 *
 * Every branch that is not `settled` or `playing` ends in an action that is
 * DISABLED with a reason, and the reason names a node or extension fact rather
 * than saying "coming soon".
 */
export function buildJudgedPanel({ slot = null, custody = null, session = null } = {}) {
  const seal = (headline, detail, code) => Object.freeze({
    state: "sealed", eyebrow: "JUDGED SIGNAL", headline, detail,
    action: Object.freeze({ label: "Play a judged run", enabled: false, reason: detail, code }),
    rounds: Object.freeze([]), settlement: null,
  });

  if (!slot || slot.state === "pending") {
    return Object.freeze({
      state: "pending", eyebrow: "JUDGED SIGNAL",
      headline: "Asking the authority",
      detail: "Reading whether a curator-committed slot is open before anything here claims to be judged.",
      action: Object.freeze({ label: "Play a judged run", enabled: false, reason: "The slot is still being read.", code: "slot-pending" }),
      rounds: Object.freeze([]), settlement: null,
    });
  }
  if (slot.state === "closed") {
    return seal(
      "No slot is open",
      "The authority publishes no curator-committed opening, so there is no judged instance to play against. " +
      "Every drill on the rack is practice, and practice settles nothing. That is the ordinary state, not a fault.",
      "slot-closed",
    );
  }
  if (slot.state !== "open") {
    return seal(
      slot.state === "refused" ? "Slot publication refused" : "No authority answered",
      slot.state === "refused"
        ? `An opening was published and this terminal would not accept it (${slot.code}). Nothing is played as judged against an opening that did not verify.`
        : `${slot.reason ?? "No authority answered"}. There is no verified opening, so nothing here can be judged.`,
      slot.code ?? "slot-unreachable",
    );
  }

  const instance =
    `Slot ${slot.slot}, commitment ${slot.commitment.slice(0, 16)}…, signed by this deployment's pinned ` +
    "curator key and checked here.";

  if (session?.state === "ready") {
    const s = session.session;
    const rounds = s.transcript.map((round, index) => Object.freeze({
      index: index + 1, code: codeText(round.guess), ...readingLabels(round),
    }));
    if (s.solved && s.settlement) {
      return Object.freeze({
        state: "settled", eyebrow: "JUDGED SIGNAL",
        headline: `Solved in ${s.roundsUsed} burst${s.roundsUsed === 1 ? "" : "s"}`,
        detail:
          `${codeText(s.settlement.code)} came back 3 LOCKED against the judged target. ${instance} ` +
          `This is the transcript a claim must be made of — the node settles the game it served, not a ` +
          `code that happens to be right. ${s.settlement.note}`,
        action: Object.freeze({
          label: "Submit this claim",
          enabled: false,
          reason:
            `Solved, and this page cannot post it. ${CUSTODY_BLOCKERS[2].what} ${CUSTODY_BLOCKERS[2].detail} ` +
            `The transcript above is durable on the node and is what a claim built elsewhere must carry.`,
          code: CUSTODY_BLOCKERS[2].code,
        }),
        rounds: Object.freeze(rounds), settlement: s.settlement,
      });
    }
    const spent = `${s.roundsUsed} of ${s.maxRounds} bursts spent, ${s.roundsRemaining} left.`;
    return Object.freeze({
      state: s.open ? "playing" : "spent", eyebrow: "JUDGED SIGNAL",
      headline: s.open ? `${s.roundsRemaining} burst${s.roundsRemaining === 1 ? "" : "s"} left` : "Out of bursts",
      detail: s.open
        ? `${spent} Every LOCKED and DRIFT below came out of the node's Lean classification against the judged target; ` +
          `this page never scores a guess. ${instance}`
        : `${spent} The run ends unsolved. Nothing was spent on chain — a losing session is simply a session with ` +
          `five spent bursts and no settlement.`,
      action: Object.freeze({
        label: s.open ? "Spend a burst" : "Play a judged run",
        enabled: false,
        reason: s.open
          ? `${CUSTODY_BLOCKERS[0].what} ${CUSTODY_BLOCKERS[0].detail}`
          : "This session is out of bursts. A new one opens against the next slot.",
        code: s.open ? CUSTODY_BLOCKERS[0].code : "session-budget-exhausted",
      }),
      rounds: Object.freeze(rounds), settlement: null,
    });
  }

  const blocker = custody?.blocker ?? CUSTODY_BLOCKERS[0];
  if (session?.state === "refused") {
    return seal("Judged session refused",
      `A session document was served and this terminal would not accept it (${session.code}). ${session.reason}. ` +
      "Nothing is shown as judged on the strength of a document that did not check out.",
      session.code);
  }
  if (!custody?.identityAvailable || session?.state === "unbound") {
    return Object.freeze({
      state: "unbound", eyebrow: "JUDGED SIGNAL",
      headline: "A slot is open, and no identity is bound",
      detail:
        `${instance} A judged run is per player — two players in one slot draw different targets — so it needs ` +
        "an identity before it can begin. No Dregg identity is bound to this terminal, so there is nothing to open " +
        "a session for. Practice is unaffected and still settles nothing.",
      action: Object.freeze({
        label: "Play a judged run", enabled: false,
        reason: "No Dregg identity is bound to this terminal. Connect the extension to bind one.",
        code: "identity-unbound",
      }),
      rounds: Object.freeze([]), settlement: null,
    });
  }
  return Object.freeze({
    state: "unplayable", eyebrow: "JUDGED SIGNAL",
    headline: "A slot is open, and this page cannot play it",
    detail:
      `${instance} An identity is bound, and judged play still cannot start from a browser. ${blocker.what} ` +
      `${blocker.detail} No key is generated here to work around it: a page-made key would have no cell, no funds ` +
      "and no post-quantum half, so it could open a session it could never settle.",
    action: Object.freeze({
      label: "Play a judged run", enabled: false,
      reason: `${blocker.what} Needs: ${blocker.needs}.`,
      code: blocker.code,
    }),
    rounds: Object.freeze([]), settlement: null,
  });
}

function element(documentRef, tag, className, textContent) {
  const node = documentRef.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

export function mountJudgedPanel(root, panel) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a judged-panel root is required");
  const documentRef = root.ownerDocument ?? globalThis.document;
  if (!documentRef?.createElement) throw new TypeError("DOM document is required");

  const card = element(documentRef, "article", `judged-panel judged-panel--${panel.state}`);
  card.dataset.state = panel.state;
  card.append(
    element(documentRef, "p", "judged-panel__eyebrow", panel.eyebrow),
    element(documentRef, "b", "judged-panel__headline", panel.headline),
    element(documentRef, "span", "judged-panel__detail", panel.detail),
  );

  if (panel.rounds.length > 0) {
    const list = element(documentRef, "ol", "judged-panel__rounds");
    for (const round of panel.rounds) {
      const item = element(documentRef, "li", "judged-round");
      item.dataset.round = String(round.index);
      item.append(
        element(documentRef, "code", "judged-round__code", round.code),
        element(documentRef, "b", "judged-round__locked", round.locked),
        element(documentRef, "small", "judged-round__drift", round.drift),
      );
      list.append(item);
    }
    card.append(list);
  }

  const button = element(documentRef, "button", "judged-panel__action", panel.action.label);
  button.type = "button";
  button.disabled = !panel.action.enabled;
  button.dataset.code = panel.action.code;
  // The reason is TEXT, not only a tooltip: a disabled control whose reason lives
  // in a `title` is a control that reads as broken to anyone who cannot hover it.
  const reason = element(documentRef, "p", "judged-panel__reason", panel.action.reason);
  reason.id = `judged-reason-${panel.action.code}`;
  button.setAttribute("aria-describedby", reason.id);
  card.append(button, reason);

  root.replaceChildren(card);
  return root;
}
