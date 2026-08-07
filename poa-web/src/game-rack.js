import { ArtifactRefusal } from "./poag1.js";
import { SHAPES } from "./descriptor-shape.js";

/**
 * ONE ANATOMY FOR EVERY GAME ON THE BOARD.
 *
 * `descriptor-shape.js` already says the important half of this out loud: shape
 * decides MECHANICS, and it deliberately does not decide PRESENTATION. This is
 * the other half. A game's presentation is a small frozen RECORD — name, one
 * flavour line, how long a sitting takes, which board it draws — and the rack
 * renders every record the same way. Adding a game is a record here plus a
 * controller in `mission-launcher.js`'s dispatch table. It is not surgery on the
 * board, and there is nowhere for a game to acquire a bespoke card.
 *
 * ⚠ A RECORD CANNOT ENROL ITS OWN GAME. Whether a card is playable is decided by
 * two things this file does not own: the SIGNED CATALOG (is there a mission?) and
 * the LAUNCHER'S DISPATCH TABLE (is there a controller?). Every combination has a
 * name and an honest label, including the one nobody wants:
 *
 *   open         enrolled by the signed catalog, controller installed.
 *   sealed       controller installed, the catalog does not enrol it yet.
 *   reserved     a berth. No controller, no mission, and — deliberately — no
 *                claim about its length or its mechanics.
 *   unsupported  the signed catalog enrols it and this client has no controller.
 *                Loud on purpose: it is the only combination that is a defect.
 *
 * A sealed slot saying "awaiting curator activation" is true. Inventing a length
 * tag or a mechanics-flavoured line for a game nobody has written is not, so a
 * reserved berth carries `session: null` and `shape: null` and the rack renders
 * that absence rather than filling it in.
 */

/** The three session lengths. A fourth is a decision, not a new string. */
export const SESSION_LENGTHS = Object.freeze({
  "quick-drill": Object.freeze({ id: "quick-drill", label: "QUICK DRILL", estimate: "~1 min" }),
  standard: Object.freeze({ id: "standard", label: "STANDARD", estimate: "~5 min" }),
  expedition: Object.freeze({ id: "expedition", label: "EXPEDITION", estimate: "~10 min" }),
});

/** The exact field set of a presentation record. Teach it; never widen it. */
export const RACK_ENTRY_KEYS = Object.freeze([
  "gameId", "name", "flavor", "session", "shape", "eyebrow", "boardLabel", "columns",
]);

export const CARD_STATES = Object.freeze(["open", "sealed", "reserved", "unsupported"]);

const SEAL_LABEL = Object.freeze({
  sealed: "AWAITING CURATOR ACTIVATION",
  reserved: "BERTH RESERVED",
  unsupported: "NO CONTROLLER INSTALLED",
});

const SEAL_COPY = Object.freeze({
  sealed: "The drill is installed and the signed catalog does not enrol it at this counter. It opens when the curator activates it — not when this page decides to show it.",
  reserved: "A berth on the rack. No drill is installed here and nothing has been emitted for it, so there is no length and no mechanics to state.",
  unsupported: "The signed catalog enrols this drill and this terminal has no controller for it. Nothing opens: a browser must never approximate a game it was not given.",
});

/** The presentation records. A new game lands here and in the dispatch table. */
export const GAME_RACK = Object.freeze([
  Object.freeze({
    gameId: "signal-triangulation",
    name: "Signal Triangulation",
    flavor: "Call a band order into the dark and read how close the echo comes back.",
    session: "standard",
    shape: SHAPES.deduction,
    eyebrow: "INTERCEPT DECK",
    boardLabel: "Signal phase controls",
    columns: 4,
  }),
  Object.freeze({
    gameId: "relay-repair",
    name: "Relay Repair",
    flavor: "One crate of spares, one dead mast, and a route that has to reach it.",
    session: "quick-drill",
    shape: SHAPES.machineFamily,
    eyebrow: "DECK RELAY",
    boardLabel: "Relay links",
    columns: 2,
  }),
  Object.freeze({
    gameId: "salvage-lock",
    name: "Salvage Lock",
    flavor: "Six plates in a cold hold, and the hold decides which two are a pair.",
    session: "standard",
    shape: SHAPES.parametric,
    eyebrow: "SALVAGE HATCH",
    boardLabel: "Six salvage-lock plates",
    columns: 3,
  }),
  Object.freeze({
    gameId: "black-box-reconstruction",
    name: "Black Box Reconstruction",
    flavor: "Ask a sealed unit yes or no until its shape has nowhere left to hide.",
    session: "standard",
    shape: SHAPES.probeOracle,
    eyebrow: "RECONSTRUCTION BAY",
    boardLabel: "Probe grid",
    columns: 6,
  }),
  // ⚠ The three records below are TAUGHT but not yet enrolled. Their controllers
  // are installed (`mission-launcher.js`) and `Emit.lean` enrols them, so they
  // render as `sealed` — "the drill is installed and the signed catalog does not
  // enrol it at this counter" — until the curator signs the counter that carries
  // their descriptors. A record may state a length and a shape as soon as a client
  // can actually play the game; what it may never do is state them for a game
  // nobody has written.
  //
  // ⚑ THERE IS NO BERTH LEFT ON THIS RACK, and that is the point at which the
  // half-taught rule stops being theoretical. Every record here now claims a
  // length and a shape, so the next game added is the first one that has to earn
  // them — and `loadRackEntry` refuses a record that claims one without the other.
  Object.freeze({
    gameId: "artificer-logic",
    name: "Artificer Logic",
    flavor: "One law hides in a sixteen-law manual. Four charges to find it, then name it.",
    session: "standard",
    shape: SHAPES.parametric,
    eyebrow: "ARTIFICER BENCH",
    boardLabel: "Eight charges and the sixteen-law manual",
    columns: 4,
  }),
  Object.freeze({
    gameId: "vent-crawl",
    name: "Vent Crawl",
    flavor: "Every rung down pays more and floods more. The odds are on the button.",
    session: "quick-drill",
    shape: SHAPES.pushYourLuck,
    eyebrow: "VENT ACCESS",
    boardLabel: "Six rungs and two verbs",
    columns: 2,
  }),
  // ⚑ Deck Descent was the one the ceremony could get WRONG, and this record is
  // the half of that repair the rack owns. `Emit.lean` already enrols it
  // (mission 5); until 2026-08-07 it had no controller, so a signed catalog
  // carrying it would have turned this card `unsupported` — "the signed catalog
  // enrols this drill and this terminal has no controller for it", the one
  // combination on this rack that is a defect. The controller is installed now,
  // so the ceremony's failure mode is gone and the card is `sealed` until it.
  Object.freeze({
    gameId: "deck-descent",
    name: "Deck Descent",
    flavor: "Nine breaths of air, three passages you cannot see, and a climb back out.",
    session: "standard",
    shape: SHAPES.parametric,
    eyebrow: "LOWER SPINE",
    boardLabel: "Nine verbs over the three-chamber shaft",
    columns: 3,
  }),
]);

function refuse(condition, code, message) {
  if (!condition) throw new ArtifactRefusal(code, message);
}

function object(value) {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function exactKeys(value, expected, at) {
  refuse(object(value), "rack-shape", `${at} must be an object`);
  const actual = Object.keys(value).sort();
  const wanted = [...expected].sort();
  refuse(
    actual.length === wanted.length && actual.every((key, index) => key === wanted[index]),
    "rack-field",
    `${at} has an unknown or missing field; the exact set is: ${wanted.join(", ")}`,
  );
}

function text(value, at, max) {
  refuse(
    typeof value === "string" && value.length > 0 && value.length <= max && !/[\n\r\t]/.test(value),
    "rack-copy",
    `${at} must be one line of at most ${max} characters`,
  );
  return value;
}

/** Parse one presentation record. The absences are checked as hard as the values. */
export function loadRackEntry(value, at = "rack entry") {
  exactKeys(value, RACK_ENTRY_KEYS, at);
  const gameId = text(value.gameId, `${at}.gameId`, 48);
  refuse(/^[a-z][a-z0-9-]*$/.test(gameId), "rack-game-id", `${at}.gameId is not a lowercase game id`);
  text(value.name, `${at}.name`, 48);
  text(value.flavor, `${at}.flavor`, 96);
  refuse(
    value.session === null || Object.hasOwn(SESSION_LENGTHS, value.session),
    "rack-session",
    `${at}.session must be null or one of: ${Object.keys(SESSION_LENGTHS).join(", ")}`,
  );
  refuse(
    value.shape === null || Object.values(SHAPES).includes(value.shape),
    "rack-shape-claim",
    `${at}.shape must be null or one of: ${Object.values(SHAPES).join(", ")}`,
  );
  // A record that knows one of these and not the other is half-taught, and the
  // half it is missing is exactly the half the board would have to guess.
  refuse(
    (value.session === null) === (value.shape === null),
    "rack-half-taught",
    `${at} declares a shape without a length or a length without a shape`,
  );
  text(value.eyebrow, `${at}.eyebrow`, 32);
  text(value.boardLabel, `${at}.boardLabel`, 64);
  refuse(Number.isSafeInteger(value.columns) && value.columns >= 1 && value.columns <= 8, "rack-columns", `${at}.columns is invalid`);
  return Object.freeze({ ...value });
}

export function loadRackEntries(entries = GAME_RACK) {
  refuse(Array.isArray(entries) && entries.length > 0, "rack-entries", "the rack needs at least one presentation record");
  const loaded = entries.map((entry, index) => loadRackEntry(entry, `rack entry ${index}`));
  refuse(new Set(loaded.map((entry) => entry.gameId)).size === loaded.length, "rack-entries", "two presentation records claim one game id");
  return Object.freeze(loaded);
}

/**
 * The trust copy, RELOCATED rather than deleted: one fold, the same rows, on
 * every card and every end screen. Every row is READ off the authenticated
 * mission — none of it is authored here, so it cannot drift into flattery.
 */
export function verificationRows(mission) {
  if (!mission) {
    return Object.freeze([
      Object.freeze({ term: "Rules authority", detail: "not enrolled in the signed catalog at this counter" }),
      Object.freeze({ term: "Run status", detail: "nothing can be played, so nothing is scored or settled" }),
    ]);
  }
  const short = typeof mission.activatedManifest === "string" ? mission.activatedManifest.slice(7, 23) : "unknown";
  return Object.freeze([
    Object.freeze({ term: "Rules authority", detail: `POAG1 ${short} · content epoch ${mission.contentEpoch}.${mission.curatorCounter}` }),
    Object.freeze({ term: "Activation", detail: String(mission.activation?.state ?? "unknown") }),
    Object.freeze({ term: "Hidden instance", detail: `${mission.instanceBinding} · ${mission.instanceDisclosure}` }),
    Object.freeze({ term: "Derived by", detail: String(mission.derivationModule ?? "unknown") }),
    Object.freeze({ term: "Reward class", detail: `${mission.rewardClass} · privacy ${mission.privacyGrade}` }),
    Object.freeze({ term: "Run status", detail: "a transcript made here is local and unsettled; it grants no score, salvage, rank, or canon" }),
  ]);
}

function bestOf(records) {
  const solved = records.filter((record) => record.outcome === "solved");
  if (solved.length === 0) return null;
  return solved.reduce((best, record) => (record.actions < best.actions ? record : best));
}

/**
 * What the card says about your runs. Practice and judged are read out of
 * SEPARATE buckets and labelled separately, because a practice best displayed
 * beside a judged best is the confusion the whole mode split exists to prevent.
 */
export function resultSummary(history) {
  const practice = Array.isArray(history?.practice) ? history.practice : [];
  const judged = Array.isArray(history?.judged) ? history.judged : [];
  if (practice.length === 0 && judged.length === 0) {
    return Object.freeze({ headline: "No run recorded in this browser", detail: "Nothing here has been played yet.", scored: false });
  }
  const last = [...practice, ...judged].reduce((latest, record) => (record.at > latest.at ? record : latest));
  const bestPractice = bestOf(practice);
  const bestJudged = bestOf(judged);
  const parts = [];
  if (bestJudged) parts.push(`judged best ${bestJudged.actions}`);
  if (bestPractice) parts.push(`practice best ${bestPractice.actions}`);
  const headline = parts.length > 0 ? parts.join(" · ") : "no completed run yet";
  const outcome = last.outcome === "solved" ? "completed" : last.outcome;
  return Object.freeze({
    headline,
    detail: `last: ${last.status} · ${outcome} in ${last.actions} action${last.actions === 1 ? "" : "s"}`,
    scored: Boolean(bestJudged),
  });
}

function cardState(enrolled, installed) {
  if (enrolled && installed) return "open";
  if (enrolled) return "unsupported";
  return installed ? "sealed" : "reserved";
}

/**
 * The whole board, in one shape. `missions` is the signed catalog, `installed`
 * is the launcher's dispatch table, `results` is this browser's local history.
 */
export function buildRack({ entries = GAME_RACK, missions = [], installed = [], results = {} } = {}) {
  const records = loadRackEntries(entries);
  const installedIds = new Set(installed);
  const byGame = new Map(missions.map((mission) => [mission.gameId, mission]));
  const known = new Set(records.map((entry) => entry.gameId));
  for (const gameId of byGame.keys()) {
    refuse(known.has(gameId), "rack-unknown-mission", `the signed catalog enrols ${gameId}, which has no presentation record`);
  }

  const cards = records.map((entry) => {
    const mission = byGame.get(entry.gameId) ?? null;
    const state = cardState(Boolean(mission), installedIds.has(entry.gameId));
    // Half-taught records may sit on the rack as berths; they may never open.
    refuse(
      state !== "open" || (entry.session !== null && entry.shape !== null),
      "rack-half-taught",
      `${entry.gameId} is enrolled and installed but its presentation record declares no length or shape`,
    );
    const session = entry.session === null ? null : SESSION_LENGTHS[entry.session];
    return Object.freeze({
      gameId: entry.gameId,
      name: entry.name,
      flavor: entry.flavor,
      eyebrow: entry.eyebrow,
      boardLabel: entry.boardLabel,
      columns: entry.columns,
      shape: entry.shape,
      session,
      sessionLabel: session ? `${session.label} ${session.estimate}` : "LENGTH NOT DECLARED",
      state,
      playable: state === "open",
      missionId: mission?.missionId ?? null,
      seal: state === "open" ? null : Object.freeze({ label: SEAL_LABEL[state], copy: SEAL_COPY[state] }),
      result: state === "open" ? resultSummary(results[entry.gameId]) : null,
      verification: verificationRows(mission),
    });
  });
  return Object.freeze(cards);
}

function element(tag, className, textContent) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (textContent !== undefined) node.textContent = textContent;
  return node;
}

/**
 * The one disclosure element. Native `<details>`, so it needs no script, no
 * inline style, and no ARIA of its own — and it is the SAME element on a card
 * and on an end screen, so a player learns it once.
 */
export function verificationFold(rows, context = null, summaryLabel = "Verification") {
  const fold = element("details", "verify-fold");
  const summary = element("summary", "verify-fold__summary", summaryLabel);
  // Seven identical "Verification" disclosures on one board is a maze by ear.
  // The label still starts with the visible text, so the two never disagree.
  if (context) summary.setAttribute("aria-label", `${summaryLabel}, ${context}`);
  fold.append(summary);
  const list = element("dl", "verify-fold__rows");
  for (const row of rows) {
    const pair = element("div", "verify-fold__row");
    pair.append(element("dt", "", row.term), element("dd", "", row.detail));
    list.append(pair);
  }
  fold.append(list);
  return fold;
}

function cardNode(card, onOpen) {
  const article = element("article", `rack-card rack-card--${card.state}`);
  article.dataset.game = card.gameId;
  article.dataset.state = card.state;

  const head = element("div", "rack-card__head");
  head.append(element("p", "rack-card__eyebrow", card.eyebrow), element("span", "rack-card__length", card.sessionLabel));
  const name = element("h3", "rack-card__name", card.name);
  const flavor = element("p", "rack-card__flavor", card.flavor);
  article.append(head, name, flavor);

  if (card.state === "open") {
    const result = element("p", "rack-card__result");
    result.append(element("b", "", card.result.headline), element("span", "", card.result.detail));
    const open = element("button", "rack-card__open", `Play ${card.name}`);
    open.type = "button";
    open.dataset.openGame = card.gameId;
    if (typeof onOpen === "function") open.addEventListener("click", () => onOpen(card.gameId));
    article.append(result, open);
  } else {
    const seal = element("p", "rack-card__seal");
    seal.append(element("b", "", card.seal.label), element("span", "", card.seal.copy));
    article.append(seal);
  }
  article.append(verificationFold(card.verification, card.name));
  return article;
}

/** Render the rack. One card shape, sealed slots included. */
export function mountGameRack(root, cards, { onOpen } = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a rack root is required");
  root.replaceChildren(...cards.map((card) => cardNode(card, onOpen)));
  return root;
}
