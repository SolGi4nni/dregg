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
 * ⚑ AND IT CAN NOW PLAY. All three things that were missing on the morning of
 * 2026-08-07 have landed, and the two that fell today are kept by name in
 * [`FALLEN_WALLS`] rather than deleted:
 *
 * 1. **The signer** — `signSignalSession`, scoped and schema-pinned to exactly
 *    the two documented statements (`extension/src/signal-session.ts`), now with
 *    a SESSION-SCOPED GRANT so a whole judged run is one consent rather than six
 *    popups. The grant is bound to `(authorityId, slot, playerKey, origin)`,
 *    bounded to 1 open + 5 guesses, and expires.
 * 2. **The routes** — `poa_signal_session::routes()` moved into `public_routes`.
 *    The bearer never authorized anything: a session write is authorized by an
 *    Ed25519 signature under the player key over a statement the node re-derives.
 *    A page holds no bearer and now needs none.
 * 3. **The carrier** — the extension's bundle is BUILT now rather than found in
 *    the tree, so `build_poa_signal_claim_turn` actually ships. Both of those are
 *    in [`FALLEN_WALLS`] with what landed.
 *
 * ⚑ AND IT CAN NOW ASK TO SETTLE. [`settleJudgedRun`] submits the transcript the
 * node served back to it through `dregg.submitPoaSignalClaim` and then watches
 * `latest_height` — the number `settlement.note` itself names. The page's whole
 * contribution is `{schema, missionId, transcript}`: it builds no carrier, signs
 * nothing, derives no cell, chooses no nonce. `claim-carrier-unbuildable` is in
 * FALLEN_WALLS not because the path runs but because it named the WRONG
 * obstacle — the page was never supposed to build a carrier.
 *
 * ⚠ THE PATH DOES NOT RUN. One wall further on, `claim-cell-underivable` stands:
 * the extension derives the player cell through `wasm.cell_id_for_pubkey`, and
 * that function has never existed in any build of the wasm. Every claim refuses
 * there, on live beta as much as here. It was MEASURED by driving the seam once
 * the carrier wall fell — it sat behind that one and was unreachable until it
 * went. See `CUSTODY_BLOCKERS`.
 *
 * So `canPlay` is routinely `true`, `canSettle` follows the provider rather than
 * this file's beliefs, and the refusal a player actually meets is rendered BY
 * NAME instead of predicted here.
 *
 * ⚑ EVERY REMAINING CONDITION IS MEASURED, not assumed. `routesReachable` comes
 * out of an actual response, and its `false` branch no longer means "the code
 * gates this" — it means THIS NODE is running a build from before the move
 * (`NODE_BEHIND`). A hardcoded `canPlay: false` would be a wall this file
 * believes in rather than one it observed, and that stays forbidden here.
 */

const SESSION_FORMAT = "POA-SIGNAL-SESSION-1";
const OPEN_STATEMENT_SCHEMA = "POA-SIGNAL-SESSION-OPEN-STATEMENT-1";
const GUESS_STATEMENT_SCHEMA = "POA-SIGNAL-SESSION-GUESS-STATEMENT-1";
const SIGNAL_CLAIM_METHOD = "poa-signal";

/**
 * `POA_SIGNAL_SCHEMA` in `extension/src/poa-signal.ts`. The page names the
 * schema and nothing else about the carrier.
 */
const CLAIM_SCHEMA = "poa-signal-claim/v1";

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
 * The provider method that signs a session statement, and the only one this page
 * will use for it. It takes STRUCTURED FIELDS, never bytes, and the extension
 * re-derives the statement itself — see `extension/src/signal-session.ts`.
 */
export const SESSION_SIGNER_METHOD = "signSignalSession";

/**
 * ⚑ WHAT THE EXTENSION MUST SHIP for this page to sign at all.
 *
 * This is NOT a wall in `CUSTODY_BLOCKERS` — those are facts about source that
 * this repo would have to change. This is a per-INSTALL capability check: an
 * extension older than 2026-08-07 has no `signSignalSession`, and the honest
 * thing to tell that player is "update the extension", not "the platform cannot
 * do this".
 */
/**
 * ⚑ WHAT THE NODE ON THIS ORIGIN MUST SERVE, per DEPLOYMENT.
 *
 * These are NOT walls in `CUSTODY_BLOCKERS` — they are not facts about source
 * that this repo would have to change, they are facts about the node answering
 * right now. The session routes are public in this repo as of 2026-08-07; a
 * deployment still answering `401` is running a build from before that, and the
 * honest thing to tell that player is "this node is behind", not "the platform
 * cannot do this".
 *
 * Keeping them distinct is the point. `session-routes-authenticated` used to
 * mean "the code gates this"; it now means "this particular node still does",
 * and those two sentences call for opposite actions.
 */
export const NODE_BEHIND = Object.freeze({
  code: "session-routes-authenticated",
  what: "This node still gates the judged session routes behind a bearer token.",
  detail:
    "`poa_signal_session::routes()` is mounted in `public_routes` as of 2026-08-07 — the bearer was " +
    "never the authorization, since every session write is an Ed25519 signature by the player key over " +
    "a statement the node re-derives. This deployment answered 401/403 anyway, so it is running a build " +
    "from before that move. The signature this page produced is correct and was refused before it was " +
    "ever checked.",
  needs: "this authority redeployed from a build at or after 2026-08-07",
});

export const NODE_SILENT = Object.freeze({
  code: "session-routes-unanswered",
  what: "Nothing on this origin answered the judged session routes.",
  detail:
    "Not a refusal and not a wall — no answer at all. A judged run is never begun on an assumption " +
    "that a route exists, so this page reports the silence rather than enabling a button that would " +
    "fail on click.",
  needs: "a reachable PoA authority on this origin",
});

export const SIGNER_ABSENT = Object.freeze({
  code: "signer-not-installed",
  what: `The installed extension exposes no \`${SESSION_SIGNER_METHOD}\`.`,
  detail:
    "Judged play needs a raw Ed25519 signature by the player key over the node's documented session " +
    "statement. The extension ships a scoped, schema-pinned signer for exactly that " +
    "(`extension/src/signal-session.ts`), but this install predates it — `window.dregg` here offers " +
    "only `getActiveIdentity()` and `signTurnV3`, neither of which produces one.",
  needs: "an extension build carrying the scoped session signer",
});

/**
 * ⚑ THE WALLS THAT HAVE FALLEN, kept by name rather than deleted.
 *
 * A wall that is simply removed from `CUSTODY_BLOCKERS` leaves no trace that it
 * was ever load-bearing, and the next reader cannot tell a wall that fell from
 * one that was never noticed. So each fallen wall keeps its `code` — the same
 * string the panel used to render — plus what actually landed. The tests INVERT
 * against these entries rather than dropping their assertions.
 */
export const FALLEN_WALLS = Object.freeze([
  Object.freeze({
    code: "no-player-message-signer",
    fell: "2026-08-07",
    was: "The extension holds the player key but will not sign a session statement with it.",
    landed:
      "A scoped, schema-pinned signer (`extension/src/signal-session.ts`). Deliberately NOT the " +
      "`signMessage(bytes)` that entry could have been read as asking for — a page that can ask for a " +
      "signature over caller-chosen bytes can ask for a signature over a transfer. What landed takes " +
      "`{kind, authorityId, slot, round, guess}` and re-derives the statement inside the extension, over " +
      "a frozen allowlist of the two session kinds, with `player_key` supplied by custody. A " +
      "session-scoped GRANT now covers one whole run — 1 open + 5 guesses, one slot, one identity, one " +
      "origin, with an expiry — so a judged run is ONE consent instead of six popups, and the grant " +
      "relaxes none of the signer's structural properties.",
  }),
  Object.freeze({
    code: "claim-carrier-unbuildable",
    fell: "2026-08-07",
    was: "The settling carrier cannot be built by this PAGE, so a solved run cannot be posted from a browser.",
    landed:
      "Nothing, in the node — and that is the finding. The wall was TRUE and NOT LOAD-BEARING: the page was " +
      "never supposed to build the carrier. `dregg.submitPoaSignalClaim` takes `{schema, missionId, " +
      "transcript}` and the EXTENSION derives the cell, nonce, receipt head, federation domain, action and " +
      "fee, paints them for consent and re-reads them off the signed bytes. The wall priced a prepare route " +
      "the page would have needed IF it built carriers; it does not. What landed is `settleJudgedRun` in " +
      "this module — the page authors identity and intent, the extension authors the carrier, and the seam " +
      "between them was already the right shape.\n\n" +
      "⚠ IT DID NOT FALL BECAUSE THE PATH WORKS. It fell because it named the wrong obstacle. The path is " +
      "still stopped, one wall further on, and that wall is `claim-cell-underivable` below — MEASURED by " +
      "driving the seam, not read off source. A wall that fell is not a leg that runs.",
  }),
  Object.freeze({
    code: "wasm-carrier-absent",
    fell: "2026-08-07",
    was:
      "The shipped `extension/dregg_wasm.js` carried 160 exports and neither `build_poa_signal_claim_turn` " +
      "nor `inspect_poa_signal_claim_turn`, so the extension refused every claim by name — on live beta too.",
    landed:
      "`84907fcf4` made the extension's bundle BUILT rather than found in the tree, plus a freshness gate " +
      "and a self-test that watch the artifact that actually ships. Measured here, not read: the in-tree " +
      "glue and the packaged zip each carry the builder 3 times, and driving " +
      "`dregg.submitPoaSignalClaim` from the beta origin no longer returns 'installed dregg WASM does not " +
      "include the PoA Signal carrier' — it now reaches three steps further into the same function.",
  }),
  Object.freeze({
    code: "session-routes-authenticated",
    fell: "2026-08-07",
    was: "The three session routes are behind the node's bearer layer; this page carries no bearer.",
    landed:
      "`poa_signal_session::routes()` moved from `protected_routes` into `public_routes` in " +
      "`node/src/api.rs`. The bearer was never the authorization: every session WRITE is an Ed25519 " +
      "signature by the player key over a statement the node RE-DERIVES, and the guess statement covers " +
      "`round`, so a replay refuses rather than spending a burst. What the bearer incidentally supplied " +
      "— abuse resistance — was replaced explicitly by `SessionAdmission`: a per-IP window, a " +
      "per-player-key window charged only AFTER the signature verifies, and a global in-flight ceiling. " +
      "The read-back is public too, which is what makes a lost response recoverable instead of a lost " +
      "burst.",
  }),
]);

/**
 * ⚑ WHY THIS BROWSER STILL CANNOT SETTLE A JUDGED RUN. Each entry is a fact
 * about the node, NOT a policy choice made here — and each names the thing that
 * would have to land for the surface below to light up unchanged.
 *
 * ⚑ TWO WALLS FELL AND ONE REMAINS. Both fallen ones are in [`FALLEN_WALLS`]
 * above, by name. What is left is not about PLAYING at all: a browser can now
 * open a judged run, spend all five bursts and read its own transcript back. It
 * cannot build the SETTLING CARRIER, and that is a different act.
 *
 * The one below is not worked around. Generating a keypair in page memory would
 * be a player key with no cell, no funds and no ML-DSA half, i.e. inventing
 * custody to make a button clickable.
 */
export const CUSTODY_BLOCKERS = Object.freeze([
  Object.freeze({
    code: "claim-cell-underivable",
    what: "The SHIPPED extension cannot derive the player's canonical cell, so every claim refuses before the node is asked.",
    detail:
      "`background.ts::clientCellIdHex` derives the player cell by calling `wasm.cell_id_for_pubkey(pubkeyHex, " +
      "\"default\")`, behind a `typeof … === \"function\"` probe that falls through to `return null`. THAT " +
      "FUNCTION HAD NEVER EXISTED — not in `wasm/src/lib.rs`, not in the glue, not in any commit: `git log -S` " +
      "over `wasm/` returned nothing, and the shipped bundle's 171 exports did not include it. So the probe " +
      "was false on every build there has ever been, `submitPoaSignalClaim` refused at `Could not derive the " +
      "active player's canonical cell` on EVERY call — live beta as much as here — and `queryBalance` failed " +
      "the same way one function up.\n\n" +
      "⚑ THE BINDING IS IN THE SOURCE NOW AND THE ARTIFACT DOES NOT CARRY IT, which is why this wall still " +
      "stands. `wasm/src/lib.rs` exports `cell_id_for_pubkey` over the same primitive the rest of the system " +
      "uses (`CellId::derive_raw(pk, blake3(domain))` — exactly `Cipherclerk::cell_id`, and at `\"default\"` " +
      "exactly `poa_signal::signal_player_cell`). The extension bundle has NOT been rebuilt against it, and a " +
      "player runs the bundle, not the source. `scripts/check-wasm-freshness.sh extension --kind no-modules` " +
      "is RED on exactly this and names the two fingerprints.\n\n" +
      "⚠ THE REBUILD IS BLOCKED, and not by anything in this path: the wasm32 workspace does not compile. A " +
      "concurrent lane's `Effect::Deshield` variant is in `turn/src/action.rs` in the working tree (13 " +
      "occurrences; ZERO in HEAD) and six `match` sites in `turn/src/executor/` and `turn/src/` have not been " +
      "extended for it. Until that lands, `cargo build --target wasm32-unknown-unknown` fails before it " +
      "reaches this crate.\n\n" +
      "⚑ MEASURED BY DRIVING, and it could not have been found any other way: it sits BEHIND the wasm-carrier " +
      "wall, so until that one fell every claim refused earlier and this refusal was unreachable. " +
      "`extension/tests/e2e/judged-signal-session.spec.ts` drives the seam and asserts the refusal by name.\n\n" +
      "⚠ A silent capability probe is what made it survivable. `clientCellIdHex` returns `null` rather than " +
      "throwing, so an absent binding reads as an ordinary negative result all the way up; nothing anywhere " +
      "says a function was looked for and not found. The binding closes this instance; the PROBE is still " +
      "silent and will hide the next one.",
    needs:
      "the extension bundle rebuilt against the `cell_id_for_pubkey` now in `wasm/src/lib.rs` " +
      "(`cd extension && ./build.sh wasm`), which needs the wasm32 workspace to compile again",
  }),
]);

/**
 * Did the session routes ANSWER this origin? A measured tri-state, never a
 * belief.
 *
 * `true` — a document was served, refused on its contents, or 404'd; either way
 * the route answered this origin.
 * `false` — 401/403: this NODE is still gating them, measured. Since the move on
 * 2026-08-07 that means a stale deployment, not a wall in the code — `NODE_BEHIND`.
 * `null` — nothing was asked, or nothing answered at all; unknown, and unknown
 * is not "reachable".
 */
export function routesReachableFrom(session) {
  if (!session || typeof session.state !== "string") return null;
  if (session.state === "unauthenticated") return false;
  if (session.state === "ready" || session.state === "none" || session.state === "refused") return true;
  return null;
}

/**
 * What custody this page actually has for judged play.
 *
 * Never throws and never invents: it reports the FIRST blocker that bites, so the
 * panel's honest reason is the one a player would hit first rather than a list.
 *
 * `session` is the result of [`loadJudgedSession`], and it is what turns route
 * reachability from an assumption into a measurement — see `routesReachableFrom`.
 * Called with one argument (nothing measured yet), `canPlay` is `false` and the
 * blocker is `NODE_SILENT`, which is the safe direction.
 *
 * ⚑ `canPlay` NOW MEANS PLAY, not settle. The bearer wall it used to be gated on
 * fell on 2026-08-07 (`FALLEN_WALLS`), so on a current deployment with the signer
 * installed and an identity bound, this returns `true` and the button is live.
 * The remaining `CUSTODY_BLOCKERS` entry is about SETTLING, which is a separate
 * act and stays disabled regardless.
 */
export function judgedCustody(provider = globalThis.window?.dregg ?? null, session = null) {
  const identityAvailable = Boolean(provider && typeof provider.getActiveIdentity === "function");
  const signerAvailable = Boolean(provider && typeof provider[SESSION_SIGNER_METHOD] === "function");
  const settlerAvailable = Boolean(provider && typeof provider[CLAIM_SUBMIT_METHOD] === "function");
  const routesReachable = routesReachableFrom(session);
  const blocker = !signerAvailable ? SIGNER_ABSENT
    : routesReachable === false ? NODE_BEHIND
    : routesReachable !== true ? NODE_SILENT
    : null;
  return Object.freeze({
    // ⚑ EVERY conjunct is observed. `canPlay` never asserts a wall this file
    // merely believes in: it is identity + signer detected on the provider, and
    // a route that actually answered.
    canPlay: identityAvailable && signerAvailable && routesReachable === true,
    // ⚑ AND SO IS `canSettle`, WHICH IS WHY IT IS NOT `false`. This page knows
    // `claim-cell-underivable` stands and STILL enables the action, because what
    // it can observe is that the provider exposes the method — and the wall lives
    // inside the extension, where no page can look. Hardcoding `false` here would
    // be the exact sin the play path already refuses: a wall this file BELIEVES in
    // rather than one it OBSERVED, and it would go on believing it for a week
    // after the wasm export lands. The click submits, the extension's refusal
    // comes back BY NAME, and the panel renders that name. A wall a player meets
    // is a wall someone fixes; a wall a docblock asserts is one that rots.
    canSettle: identityAvailable && settlerAvailable,
    identityAvailable,
    signerAvailable,
    settlerAvailable,
    routesReachable,
    // A settled deployment with everything present still names the SETTLING wall,
    // because that is the next thing this page cannot do.
    blocker: blocker ?? CUSTODY_BLOCKERS[0],
    settleBlocker: settlerAvailable ? CUSTODY_BLOCKERS[0] : SETTLER_ABSENT,
    blockers: CUSTODY_BLOCKERS,
    fellAlready: FALLEN_WALLS,
  });
}

/**
 * Ask the extension for a signature over one session statement, and CHECK IT
 * BEFORE USING IT.
 *
 * The extension re-derives the statement from the structured fields; so does
 * this page (`openStatementMessage` / `guessStatementMessage`). Two independent
 * derivations of the same pinned node encoding, compared here — a mismatch is a
 * refusal on this side rather than a 401 from the authority that would read like
 * a node fault. That comparison is the whole reason the extension returns the
 * statement text alongside the signature.
 *
 * Never throws: every failure is a STATE, the discipline `loadJudgedSession`
 * follows.
 */
export async function requestSessionSignature({ provider, kind, authorityId, slot, round = null, guess = null }) {
  if (!provider || typeof provider[SESSION_SIGNER_METHOD] !== "function") {
    return Object.freeze({ state: "unsigned", code: SIGNER_ABSENT.code, reason: SIGNER_ABSENT.what });
  }
  if (kind !== "open" && kind !== "guess") {
    return Object.freeze({ state: "unsigned", code: "session-kind", reason: `unknown session statement kind: ${kind}` });
  }
  const request = kind === "open"
    ? { kind, authorityId, slot }
    : { kind, authorityId, slot, round, guess };
  let signed;
  try {
    signed = await provider[SESSION_SIGNER_METHOD](request);
  } catch (error) {
    return Object.freeze({
      state: error?.code === "user-declined" ? "declined" : "unsigned",
      code: error?.code ?? "sign-failed",
      reason: error?.message ?? "the extension refused to sign this session statement",
    });
  }
  const playerKey = signed?.playerKeyHex;
  if (typeof playerKey !== "string" || !HEX_32.test(playerKey)) {
    return Object.freeze({ state: "unsigned", code: "session-player", reason: "the signer returned no player key" });
  }
  if (typeof signed?.signatureHex !== "string" || !/^[0-9a-f]{128}$/.test(signed.signatureHex)) {
    return Object.freeze({
      state: "unsigned", code: "session-signature",
      reason: "the signer returned something that is not a 128-hex-digit Ed25519 signature",
    });
  }
  const expected = kind === "open"
    ? openStatementMessage({ authorityId, slot, playerKey })
    : guessStatementMessage({ authorityId, slot, playerKey, round, guess });
  if (signed.statement !== expected) {
    return Object.freeze({
      state: "unsigned", code: "session-statement-mismatch",
      reason:
        "the extension signed a statement this page does not agree is the documented one, so it is not " +
        "sent. Two derivations of the node's encoding disagreed; one of them has drifted.",
    });
  }
  return Object.freeze({ state: "signed", playerKey, statement: expected, signature: signed.signatureHex });
}

async function postSession({ path, body, authorityId, commitment, baseUrl, fetchImpl, prefix }) {
  const url = new URL(`${prefix}${path}`, baseUrl ?? globalThis.location?.href ?? "https://invalid.local/");
  let document;
  try {
    const response = await fetchImpl(url, {
      method: "POST",
      cache: "no-store",
      credentials: "same-origin",
      headers: { "content-type": "application/json" },
      body: JSON.stringify(body),
    });
    if (response?.status === 401 || response?.status === 403) {
      return Object.freeze({
        state: "unauthenticated", code: NODE_BEHIND.code,
        reason: NODE_BEHIND.what,
      });
    }
    const text = await response.text();
    if (!response?.ok) {
      // The node's refusals are NAMED, and the name is the useful half — a
      // `session-round-mismatch` is a replayed burst, not an outage.
      let named = null;
      try { named = JSON.parse(text); } catch { named = null; }
      return Object.freeze({
        state: "refused",
        code: typeof named?.reason === "string" ? named.reason : "session-status",
        reason: typeof named?.detail === "string" ? named.detail : `The authority answered HTTP ${response?.status ?? "nothing"}`,
      });
    }
    document = JSON.parse(text);
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

/**
 * Open or resume a judged run: sign the open statement, POST it, parse what
 * comes back against the slot this terminal verified.
 *
 * ⚑ As of 2026-08-07 this POST is expected to be SERVED: the route is public and
 * the player's signature is the whole authorization. An `unauthenticated` result
 * is no longer the ordinary state — it means the node answering here predates
 * the move (`NODE_BEHIND`), and the page says so rather than blaming the wall
 * that used to be here.
 */
export async function openJudgedSession({
  provider, authorityId, commitment, slot, baseUrl,
  fetchImpl = globalThis.fetch, prefix = "/node",
} = {}) {
  if (typeof authorityId !== "string" || !HEX_32.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "session-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "session-fetch", reason: "No fetch is available in this environment" });
  }
  const signed = await requestSessionSignature({ provider, kind: "open", authorityId, slot });
  if (signed.state !== "signed") return signed;
  return postSession({
    path: `/api/poa/signal/${authorityId}/session/open`,
    body: { player_key: signed.playerKey, signature: signed.signature },
    authorityId, commitment, baseUrl, fetchImpl, prefix,
  });
}

/**
 * Spend one burst: sign the guess statement for THIS round, POST it, parse the
 * transcript that comes back.
 *
 * `round` is the number of bursts ALREADY spent — read it off the session
 * document's `roundsUsed`, never counted here. It is inside the signature, which
 * is why a replayed request refuses as `session-round-mismatch` rather than
 * spending a second burst.
 */
export async function spendJudgedBurst({
  provider, authorityId, commitment, slot, round, guess, baseUrl,
  fetchImpl = globalThis.fetch, prefix = "/node",
} = {}) {
  if (typeof authorityId !== "string" || !HEX_32.test(authorityId)) {
    return Object.freeze({ state: "unreachable", code: "session-authority", reason: "This terminal has no authority id to ask about" });
  }
  if (typeof fetchImpl !== "function") {
    return Object.freeze({ state: "unreachable", code: "session-fetch", reason: "No fetch is available in this environment" });
  }
  const signed = await requestSessionSignature({ provider, kind: "guess", authorityId, slot, round, guess });
  if (signed.state !== "signed") return signed;
  return postSession({
    path: `/api/poa/signal/${authorityId}/session/guess`,
    body: { player_key: signed.playerKey, round, guess, signature: signed.signature },
    authorityId, commitment, baseUrl, fetchImpl, prefix,
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
        code: NODE_BEHIND.code,
        reason: NODE_BEHIND.what,
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

/**
 * The provider method that SETTLES a solved run, and the only one this page will
 * use for it.
 *
 * ⚑ THE PAGE DOES NOT BUILD THE CARRIER AND MUST NOT. A claim is a
 * postcard-encoded `SignedTurn` under a hybrid Ed25519 + ML-DSA-65
 * authorization; the extension derives the player cell, the live nonce, the
 * receipt head, the federation domain, the action and the fee itself, paints
 * them for consent, and re-reads them off the SIGNED bytes before submitting
 * (`extension/src/background.ts::submitPoaSignalClaim`). What crosses this seam
 * is `{schema, missionId, transcript}` — the bounded public intent — and every
 * field of it is copied off the document the NODE served.
 */
export const CLAIM_SUBMIT_METHOD = "submitPoaSignalClaim";

export const SETTLER_ABSENT = Object.freeze({
  code: "settler-not-installed",
  what: `The installed extension exposes no \`${CLAIM_SUBMIT_METHOD}\`.`,
  detail:
    "Settling a solved run is a signed turn against the PoA federation, and the carrier is built inside " +
    "the extension by the shipped wasm. This install predates that method, so there is nothing to submit " +
    "through — and no page-side builder is a substitute, because the ML-DSA half cannot be produced here.",
  needs: "an extension build exposing the transcript-carrying claim path",
});

/**
 * ⚑ THE CLAIM IS A RE-SHAPING OF SERVED BYTES, NOT A CONSTRUCTION.
 *
 * Every field comes off `settlement`, which `parseSettlement` already checked
 * round-for-round against the transcript the player actually played. There is no
 * parameter here for a caller-chosen transcript, and that absence is the point:
 * a page cannot submit a code it did not play through the session, because this
 * function has no way to be told one. A claim assembled from anything else is a
 * claim the node refuses (`verify_claim_transcript_was_played`), and the refusal
 * would read like a judge failure rather than a client bug.
 *
 * The `{low, mid, high}` → `[low, mid, high]` turn is the extension's wire order
 * (`PoASignalCode` in `extension/src/poa-signal.ts`), pinned by test.
 */
export function settlementClaim(settlement) {
  refuse(object(settlement), "settle-unsolved",
    "there is no settlement to submit; an unsolved run has nothing to claim");
  return Object.freeze({
    schema: CLAIM_SCHEMA,
    missionId: settlement.missionId,
    transcript: Object.freeze(settlement.transcript.map((code) => Object.freeze([code.low, code.mid, code.high]))),
  });
}

/**
 * `latest_height` off `GET /status` — THE NUMBER THE NODE ITSELF NAMES.
 *
 * Not a number this page chose. `poa_signal_session.rs` writes it into every
 * settlement it serves: "`accepted: true` from that route is admission staging
 * and settles nothing; the number that bites is `latest_height` off GET /status
 * AFTER finalization". So the page reads exactly that, and `settlement.note`
 * carrying the same sentence is what a player is shown.
 *
 * ⚠ `latest_height` is the attested-root height, NOT `dag_height`. A node
 * producing heartbeat blocks moves `dag_height` while nothing settles; reading
 * the wrong one of that pair is how "the chain is running" gets said about a
 * chain that has recorded no turn.
 *
 * Never throws: an unreadable status is `null`, which is "unknown", never zero.
 */
export async function readLatestHeight({ baseUrl, fetchImpl = globalThis.fetch, prefix = "/node" } = {}) {
  if (typeof fetchImpl !== "function") return null;
  try {
    const url = new URL(`${prefix}/status`, baseUrl ?? globalThis.location?.href ?? "https://invalid.local/");
    const response = await fetchImpl(url, { cache: "no-store", credentials: "same-origin" });
    if (!response?.ok) return null;
    const body = JSON.parse(await response.text());
    const height = body?.latest_height;
    return Number.isSafeInteger(height) && height >= 0 ? height : null;
  } catch {
    return null;
  }
}

/** How long the page waits for `latest_height` to move, and how often it looks. */
const SETTLE_POLL_MS = 750;
const SETTLE_DEADLINE_MS = 20_000;

/**
 * SETTLE A SOLVED JUDGED RUN: submit the transcript the node served back to it,
 * through the extension, then watch the one number that says it stuck.
 *
 * The page's whole contribution is `{schema, missionId, transcript}` and the
 * decision to send it. It signs nothing, derives no cell, chooses no nonce, and
 * never scores a guess.
 *
 * ⚑ TWO MEASUREMENTS, AND THEY ANSWER DIFFERENT QUESTIONS. The extension returns
 * `admission` (did the node's ingress accept the signed bytes) and `transition`
 * (did the Signal head grow a transition for this turn). This page adds the
 * third and last one: did `latest_height` MOVE. Admission is staging and can be
 * rolled back; a transition is the authority's own fold; only the attested root
 * moving is finalization. Reporting the first as if it were the third is exactly
 * what `settlement.note` exists to forbid, so all three are reported separately
 * and none is collapsed into the others.
 *
 * Never throws: every failure is a STATE, the discipline the rest of this module
 * follows. The extension's named refusal is carried through VERBATIM rather than
 * re-worded — "the installed dregg WASM does not include the PoA Signal carrier"
 * is a fact about the artifact a player has, and a paraphrase loses it.
 */
export async function settleJudgedRun({
  provider, session, baseUrl, fetchImpl = globalThis.fetch, prefix = "/node",
  pollMs = SETTLE_POLL_MS, deadlineMs = SETTLE_DEADLINE_MS,
} = {}) {
  if (!provider || typeof provider[CLAIM_SUBMIT_METHOD] !== "function") {
    return Object.freeze({ state: "unsettleable", code: SETTLER_ABSENT.code, reason: SETTLER_ABSENT.what });
  }
  if (!object(session) || session.settlement === null || session.settlement === undefined) {
    return Object.freeze({
      state: "unsettleable", code: "settle-unsolved",
      reason: "this run carries no settlement, so there is nothing to claim",
    });
  }
  let claim;
  try {
    claim = settlementClaim(session.settlement);
  } catch (error) {
    return Object.freeze({
      state: "unsettleable", code: error?.code ?? "settle-unsolved",
      reason: error?.message ?? "this run cannot be turned into a claim",
    });
  }

  // BEFORE the submit, so the comparison afterwards is against a height this
  // page actually observed rather than against zero. A `null` baseline means the
  // status was unreadable, and then no movement can be claimed either way.
  const heightBefore = await readLatestHeight({ baseUrl, fetchImpl, prefix });

  let result;
  try {
    result = await provider[CLAIM_SUBMIT_METHOD](claim);
  } catch (error) {
    return Object.freeze({
      state: "refused",
      code: error?.code ?? "settle-failed",
      reason: error?.message ?? "the extension refused to submit this claim",
      claim,
    });
  }
  if (!object(result) || result.admission === "refused") {
    return Object.freeze({
      state: "refused",
      code: "settle-refused",
      // VERBATIM. The extension's refusals name the exact artifact or node fact
      // that bit; re-wording one turns a diagnosis into a shrug.
      reason: result?.error ?? "the extension refused this claim without saying why",
      claim,
    });
  }

  const heightAfter = heightBefore === null
    ? null
    : await pollForHeightAbove(heightBefore, { baseUrl, fetchImpl, prefix }, pollMs, deadlineMs);

  return Object.freeze({
    state: "submitted",
    claim,
    turnId: result.turnId ?? null,
    admission: result.admission,
    transition: result.transition,
    transitionSequence: result.transitionSequence ?? null,
    heightBefore,
    heightAfter,
    // ⚑ THE ONLY CONJUNCT THAT MEANS SETTLED. `admission: "admitted"` is staging,
    // and a page that rendered it as a result would be telling a player their run
    // landed on a chain that has not recorded it.
    finalized: heightBefore !== null && heightAfter !== null && heightAfter > heightBefore,
  });
}

async function pollForHeightAbove(baseline, options, pollMs, deadlineMs) {
  const deadline = Date.now() + deadlineMs;
  let latest = baseline;
  for (;;) {
    const height = await readLatestHeight(options);
    if (height !== null) {
      latest = height;
      if (height > baseline) return height;
    }
    if (Date.now() >= deadline) return latest;
    await new Promise((resolve) => setTimeout(resolve, pollMs));
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
 * What a finished settle attempt says, in one line each.
 *
 * ⚑ THE THREE ANSWERS ARE KEPT APART. `admission` is the node's ingress taking
 * the bytes, `transition` is the Signal head folding them, `finalized` is
 * `latest_height` moving — and only the last one settles anything. Collapsing
 * them into "submitted ✓" is precisely what the node's own settlement note
 * forbids, so the copy names which of the three actually happened.
 */
function settleOutcomeHeadline(settle) {
  if (settle.state === "submitted") {
    return settle.finalized ? "Settled on chain" : "Submitted, not yet finalized";
  }
  return settle.state === "refused" ? "The claim was refused" : "This run cannot be submitted";
}

function settleOutcomeDetail(settle) {
  if (settle.state !== "submitted") {
    // VERBATIM, never re-worded: the extension's refusals name the exact artifact
    // or node fact that bit, and that name is the whole diagnostic value.
    return `${settle.reason} (${settle.code})`;
  }
  const height = settle.heightBefore === null
    ? "`latest_height` could not be read, so nothing here claims the chain moved"
    : settle.finalized
      ? `\`latest_height\` moved ${settle.heightBefore} → ${settle.heightAfter}, which is the number that settles it`
      : `\`latest_height\` has not moved off ${settle.heightBefore} yet — admission is staging and settles nothing`;
  const transition = settle.transition === "observed"
    ? `the authority folded it as transition ${settle.transitionSequence}`
    : "the authority has not folded a transition for it yet";
  return `The node admitted the signed carrier (${settle.admission}), ${transition}, and ${height}.`;
}

/**
 * The judged panel: one state, one honest sentence about what a player may do.
 *
 * Every branch that is not `settled` or `playing` ends in an action that is
 * DISABLED with a reason, and the reason names a node or extension fact rather
 * than saying "coming soon".
 *
 * ⚑ THE PLAY ACTION IS LIVE. It follows `custody.canPlay` — identity + signer
 * detected on the provider and a route that ACTUALLY ANSWERED — and since the
 * session routes went public on 2026-08-07 that conjunction is the ordinary case
 * rather than the aspirational one. A 401 here now means the node predates the
 * move (`NODE_BEHIND`), and the copy says that instead of blaming a wall that is
 * gone. Settling remains disabled regardless: that is `CARRIER_WALL`, and it was
 * always a separate wall from playing.
 */
export function buildJudgedPanel({ slot = null, custody = null, session = null, settle = null } = {}) {
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
      const canSettle = custody?.canSettle === true;
      const settleBlocker = custody?.settleBlocker ?? SETTLER_ABSENT;
      return Object.freeze({
        state: settle ? "settling" : "settled", eyebrow: "JUDGED SIGNAL",
        headline: settle
          ? settleOutcomeHeadline(settle)
          : `Solved in ${s.roundsUsed} burst${s.roundsUsed === 1 ? "" : "s"}`,
        detail:
          `${codeText(s.settlement.code)} came back 3 LOCKED against the judged target. ${instance} ` +
          `This is the transcript a claim must be made of — the node settles the game it served, not a ` +
          `code that happens to be right. ${s.settlement.note}` +
          (settle ? ` ${settleOutcomeDetail(settle)}` : ""),
        action: Object.freeze({
          label: "Submit this claim",
          // ⚑ LIVE when the provider carries the method. What this page sends is
          // `{schema, missionId, transcript}` off the document above; the
          // extension builds, prices, paints and signs the carrier.
          enabled: canSettle && !settle,
          reason: !canSettle
            ? `${settleBlocker.what} ${settleBlocker.detail}`
            : settle
              ? settleOutcomeDetail(settle)
              : "Submits the transcript the node served back to it, through your extension: it derives your " +
                "cell, nonce and receipt head, shows you the whole run before signing, and posts the signed " +
                "carrier. This page never scores a guess and never builds the carrier.",
          code: !canSettle ? settleBlocker.code : settle ? (settle.code ?? "settle-submitted") : "settle-claim",
        }),
        rounds: Object.freeze(rounds), settlement: s.settlement, settle: settle ?? null,
      });
    }
    const spent = `${s.roundsUsed} of ${s.maxRounds} bursts spent, ${s.roundsRemaining} left.`;
    const canSpend = s.open && custody?.canPlay === true;
    const spendBlocker = custody?.blocker ?? NODE_SILENT;
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
        enabled: canSpend,
        reason: !s.open
          ? "This session is out of bursts. A new one opens against the next slot."
          : canSpend
            ? "One of five bursts, signed by your player key and classified against the judged target. " +
              "Nothing is spent on chain until you solve and settle."
            : `${spendBlocker.what} ${spendBlocker.detail}`,
        code: !s.open ? "session-budget-exhausted" : canSpend ? "session-guess" : spendBlocker.code,
      }),
      rounds: Object.freeze(rounds), settlement: null,
    });
  }

  const blocker = custody?.blocker ?? NODE_SILENT;
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
  if (custody?.canPlay === true) {
    // Identity bound, signer installed, and the route ANSWERED. Every
    // precondition this page can observe is met, so the action is live: the
    // click signs the open statement with the player key and POSTs it.
    return Object.freeze({
      state: "openable", eyebrow: "JUDGED SIGNAL",
      headline: "A slot is open, and you can play it",
      detail:
        `${instance} Opening a run asks your extension to sign one documented statement with your player key — ` +
        "it moves no DREGG and authorizes no turn, it proves the run is yours so nobody else can burn your five " +
        "bursts. Every LOCKED and DRIFT after that comes out of the node's Lean classification; this page never " +
        "scores a guess.",
      action: Object.freeze({
        label: "Play a judged run", enabled: true,
        reason:
          "Five bursts against the judged target, per player. Nothing is spent on chain until you solve, and " +
          "settling is a separate act.",
        code: "session-open",
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
