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
 * A sealed slot saying the curator has not opened it is true. Inventing a length
 * tag or a mechanics-flavoured line for a game nobody has written is not, so a
 * reserved berth carries `session: null` and `shape: null` and the rack renders
 * that absence rather than filling it in.
 *
 * ⚑ AND TWO STATES THAT ARE NOT ABOUT THE GAME AT ALL. Those four answer
 * "enrolled? installed?" — a question with no answer until the signed catalog has
 * been READ. On 2026-08-09 the live beta could not decode counter 10, and every
 * card on it said AWAITING CURATOR ACTIVATION: *"the signed catalog does not
 * enrol it at this counter."* The catalog enrolled all seven. The terminal blamed
 * the curator for its own decoding failure, in a sentence written to be
 * reassuring, under a banner that said MISSION AUTHORITY SEALED — and the code
 * that did it carried the comment "with no authenticated catalog every slot is
 * sealed, which is the honest picture."
 *
 *   checking     the signed catalog has not been read yet. Nothing is open or
 *                closed; this terminal does not know.
 *   refused      the catalog was read and refused. Still not a claim about the
 *                curator: it names the refusal and says the fault is HERE.
 *
 * So the rack takes a `standing`, and no card may state a reason the terminal has
 * not established. An honest absence is a feature; an honest-sounding absence
 * standing in for a fault is the failure it is easiest to ship.
 *
 * ⚑ THE WORDS ON A CARD ARE NOT THE WORDS IN THIS FILE'S HEAD. Every state above
 * keeps its name in code and says its piece in the ship's own register — see
 * `docs/reference/POA-VOICE-2026-08-09.md`. "The signed content epoch did not
 * authenticate at this counter" and "the curator's manifest did not check out
 * here" are the same claim; only one of them can be read by somebody who came to
 * play a game. What may never move is WHO DECIDED: a curator decision, a fault on
 * this side, and a thing not yet known are three sentences and stay three.
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

export const CARD_STATES = Object.freeze(["open", "sealed", "reserved", "unsupported", "checking", "refused"]);

/** What this terminal knows about the signed catalog. `ready` means it read one. */
export const CATALOG_STANDINGS = Object.freeze(["pending", "ready", "refused"]);

const SEAL_LABEL = Object.freeze({
  sealed: "THE CURATOR HAS NOT OPENED THIS",
  reserved: "EMPTY BERTH",
  unsupported: "THIS TERMINAL CANNOT RUN IT",
  checking: "READING THE MANIFEST",
  refused: "THIS TERMINAL COULD NOT READ THE MANIFEST",
});

const SEAL_COPY = Object.freeze({
  sealed: "The drill is built and sitting here. It is not on the manifest the curator signed, so it stays shut — it opens when the curator opens it, not when this page decides to show it.",
  reserved: "An empty berth on the rack. Nothing is built for this slot and nothing has been written for it, so there is no length and no shape to put on the card.",
  unsupported: "The curator has opened this drill and this terminal has no way to run it. Nothing opens: a browser must never approximate a game it was not given.",
  checking: "Nothing here is open or shut yet. This terminal is still checking the curator's signature on the manifest, and until that is done it does not know what the curator opened.",
  refused: "The curator's manifest did not check out here, so this terminal cannot say what the curator opened or held back. That is a fault on this side of the glass, not a closed drill.",
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
 * Plain words for the tags the catalog emits, and the tag kept beside them.
 *
 * ⚠ BOTH, NEVER ONE. `oracle-only` means something exact and a player cannot read
 * it; "never named on screen" is readable and is not the emitted token, so it
 * cannot be matched against the bytes. A tag with no gloss here falls through
 * VERBATIM rather than being dressed in a nearby sentence — this table teaches
 * words for tags it has been taught, and says nothing about the rest.
 */
const ACTIVATION_COPY = Object.freeze({
  "detached-signature-required": "a curator signature kept outside the rules, so the rules cannot open themselves",
});
const BINDING_COPY = Object.freeze({
  "per-run-hidden-draw": "drawn fresh for every run",
});
const DISCLOSURE_COPY = Object.freeze({
  "oracle-only": "never named on screen — the table answers, it does not show",
  "per-run-open": "named to you when the run opens",
});

function glossed(table, tag) {
  const key = String(tag ?? "unknown");
  const words = table[key];
  return words ? `${words} (${key})` : key;
}

/**
 * The trust copy, RELOCATED rather than deleted: one fold, the same rows, on
 * every card and every end screen. Every row is READ off the authenticated
 * mission — none of it is authored here, so it cannot drift into flattery.
 */
export function verificationRows(mission, standing = "ready") {
  if (!mission) {
    // ⚠ The same trap as the seal copy: "the curator has not opened it" is a claim
    // about the CURATOR, and it is only available once a catalog has been read.
    const detail = {
      pending: "not established — this terminal is still checking the curator's manifest",
      refused: "not established — the curator's manifest did not check out here, so this terminal cannot say",
      ready: "not on the manifest the curator signed",
    }[standing] ?? "not established";
    return Object.freeze([
      Object.freeze({ term: "Rules", detail }),
      Object.freeze({ term: "What a run here is worth", detail: "nothing can be played, so nothing is scored and nothing settles" }),
    ]);
  }
  const short = typeof mission.activatedManifest === "string" ? mission.activatedManifest.slice(7, 23) : "unknown";
  return Object.freeze([
    Object.freeze({ term: "Rules", detail: `POAG1 ${short} · manifest revision ${mission.contentEpoch}.${mission.curatorCounter}` }),
    Object.freeze({ term: "Opened by", detail: glossed(ACTIVATION_COPY, mission.activation?.state) }),
    Object.freeze({ term: "The hidden answer", detail: `${glossed(BINDING_COPY, mission.instanceBinding)} · ${glossed(DISCLOSURE_COPY, mission.instanceDisclosure)}` }),
    Object.freeze({ term: "Drawn by", detail: String(mission.derivationModule ?? "unknown") }),
    Object.freeze({ term: "Reward", detail: `${mission.rewardClass} · privacy ${mission.privacyGrade}` }),
    Object.freeze({ term: "What a run here is worth", detail: "a run played here stays in this browser: no score, no salvage, no rank, and nothing written to the ship" }),
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
    // `recorded: false` is what lets the card DRAW NOTHING here. Seven cards each
    // carrying a bordered panel that says "nothing has been played yet" is seven
    // pieces of furniture built for an absence — and on a first visit that is the
    // whole board. The absence of a record needs no box; a record gets one.
    return Object.freeze({ headline: "Not played here yet", detail: "This browser has no record of a run.", scored: false, recorded: false });
  }
  const last = [...practice, ...judged].reduce((latest, record) => (record.at > latest.at ? record : latest));
  const bestPractice = bestOf(practice);
  const bestJudged = bestOf(judged);
  // ⚠ THE UNIT IS SAID. "judged best 4" reads as a score of four; the number is
  // an ACTION COUNT and lower is better, which is the opposite reading.
  const parts = [];
  if (bestJudged) parts.push(`judged best ${actionCount(bestJudged.actions)}`);
  if (bestPractice) parts.push(`practice best ${actionCount(bestPractice.actions)}`);
  const headline = parts.length > 0 ? parts.join(" · ") : "nothing solved yet";
  const outcome = last.outcome === "solved" ? "solved" : last.outcome;
  return Object.freeze({
    headline,
    detail: `Last run: ${last.status}, ${outcome} in ${actionCount(last.actions)}.`,
    scored: Boolean(bestJudged),
    recorded: true,
  });
}

/** `1 action`, never `1 actions`. */
function actionCount(actions) {
  return `${actions} action${actions === 1 ? "" : "s"}`;
}

function cardState(standing, enrolled, installed) {
  // Enrolment is unknown until a catalog is read, and a card may not guess.
  if (standing === "pending") return "checking";
  if (standing === "refused") return "refused";
  if (enrolled && installed) return "open";
  if (enrolled) return "unsupported";
  return installed ? "sealed" : "reserved";
}

/**
 * The whole board, in one shape. `missions` is the signed catalog, `installed`
 * is the launcher's dispatch table, `results` is this browser's local history,
 * and `standing` is whether a catalog has been read at all.
 */
export function buildRack({ entries = GAME_RACK, missions = [], installed = [], results = {}, standing = "ready" } = {}) {
  refuse(CATALOG_STANDINGS.includes(standing), "rack-standing", `the rack was given an unknown catalog standing: ${standing}`);
  const records = loadRackEntries(entries);
  const installedIds = new Set(installed);
  const byGame = new Map(missions.map((mission) => [mission.gameId, mission]));
  const known = new Set(records.map((entry) => entry.gameId));
  for (const gameId of byGame.keys()) {
    refuse(known.has(gameId), "rack-unknown-mission", `the signed catalog enrols ${gameId}, which has no presentation record`);
  }
  // Missions with no standing to have come from is the two disagreeing, and the
  // board must not pick one: a caller that has read a catalog says so.
  refuse(
    standing === "ready" || byGame.size === 0,
    "rack-standing",
    `the rack was handed ${byGame.size} enrolled missions under a "${standing}" catalog`,
  );

  const cards = records.map((entry) => {
    const mission = byGame.get(entry.gameId) ?? null;
    const state = cardState(standing, Boolean(mission), installedIds.has(entry.gameId));
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
      sessionLabel: session ? `${session.label} ${session.estimate}` : "NO LENGTH YET",
      state,
      playable: state === "open",
      missionId: mission?.missionId ?? null,
      seal: state === "open" ? null : Object.freeze({ label: SEAL_LABEL[state], copy: SEAL_COPY[state] }),
      result: state === "open" ? resultSummary(results[entry.gameId]) : null,
      verification: verificationRows(mission, standing),
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
  // The group heading above already names the length, so the card badge carries
  // the ESTIMATE only. A berth has neither, and its badge says so at full length
  // rather than shrinking the absence into something that scans as a value.
  head.append(element("p", "rack-card__eyebrow", card.eyebrow), element("span", "rack-card__length", card.session ? card.session.estimate : card.sessionLabel));
  const name = element("h3", "rack-card__name", card.name);
  const flavor = element("p", "rack-card__flavor", card.flavor);
  article.append(head, name, flavor);

  if (card.state === "open") {
    if (card.result.recorded) {
      const result = element("p", "rack-card__result");
      result.append(element("b", "", card.result.headline), element("span", "", card.result.detail));
      article.append(result);
    }
    const open = element("button", "rack-card__open", `Play ${card.name}`);
    open.type = "button";
    open.dataset.openGame = card.gameId;
    if (typeof onOpen === "function") open.addEventListener("click", () => onOpen(card.gameId));
    article.append(open);
  } else {
    const seal = element("p", "rack-card__seal");
    seal.append(element("b", "", card.seal.label), element("span", "", card.seal.copy));
    article.append(seal);
  }
  article.append(verificationFold(card.verification, card.name));
  return article;
}

/**
 * The rack's ONE ordering axis, and why it is this one.
 *
 * Four cards were four equal boxes and that was fine. Seven are not: a board with
 * no hierarchy makes a player read all seven flavour lines to answer the question
 * they actually arrived with, which is *how long have I got*. The rack's own
 * heading already promises that answer — "short drills you can finish standing
 * up, and longer ones for a quiet watch" — and every record already declares it.
 *
 * So the grouping is READ OFF the records, shortest sitting first, and a length
 * nothing is installed under does not appear. It invents no category, sorts on no
 * quality judgement, and cannot rank one drill above another.
 */
function rackGroups(cards) {
  const order = [...Object.keys(SESSION_LENGTHS), null];
  return order
    .map((id) => ({
      id: id ?? "unstated",
      label: id === null ? "NO LENGTH YET" : SESSION_LENGTHS[id].label,
      estimate: id === null ? null : SESSION_LENGTHS[id].estimate,
      cards: cards.filter((card) => (card.session?.id ?? null) === id),
    }))
    .filter((group) => group.cards.length > 0);
}

function groupNode(group, onOpen) {
  const section = element("section", "rack-group");
  section.dataset.session = group.id;
  const heading = element("h2", "rack-group__head");
  heading.append(element("span", "rack-group__label", group.label));
  if (group.estimate) heading.append(element("span", "rack-group__estimate", group.estimate));
  // The count is a fact about this board, and it is what tells a scanning eye
  // that a short row is the end of a group rather than a card that failed to draw.
  heading.append(element("span", "rack-group__count", `${group.cards.length}`));
  // A bare "2" beside a length reads as a number by eye and as nothing by ear.
  // The label is the visible text expanded, never a different claim.
  const spoken = [group.label.toLowerCase(), group.estimate, `${group.cards.length} drill${group.cards.length === 1 ? "" : "s"}`];
  heading.setAttribute("aria-label", spoken.filter(Boolean).join(", "));
  const grid = element("div", "rack-group__cards");
  grid.append(...group.cards.map((card) => cardNode(card, onOpen)));
  section.append(heading, grid);
  return section;
}

/** Render the rack. One card shape, sealed slots included. */
export function mountGameRack(root, cards, { onOpen } = {}) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a rack root is required");
  root.replaceChildren(...rackGroups(cards).map((group) => groupNode(group, onOpen)));
  return root;
}

/**
 * The board could not be built at all.
 *
 * ⚠ This exists because the alternative shipped: `buildRack` throwing left an
 * EMPTY rack mounted and a line in the console, so the entire section of the page
 * simply was not there and nothing on screen said why. A rack refusal is a defect
 * in this client — never a curator decision — and it says so in those words.
 */
export function mountRackRefusal(root, error) {
  if (!root || typeof root.replaceChildren !== "function") throw new TypeError("a rack root is required");
  const notice = element("section", "rack-refusal");
  notice.setAttribute("role", "alert");
  notice.append(
    element("p", "rack-refusal__label", "THIS TERMINAL COULD NOT BUILD THE RACK"),
    element("p", "rack-refusal__copy", "The board is empty because this terminal could not put it together, not because the curator shut anything. The fault is on this side of the glass, and this is what broke:"),
    element("code", "rack-refusal__code", error?.code ? `${error.code}: ${error.message}` : String(error?.message ?? error)),
  );
  root.replaceChildren(notice);
  return root;
}
