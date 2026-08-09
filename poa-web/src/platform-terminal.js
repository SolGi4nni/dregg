import {
  BUILTIN_FIXTURE_SHA256,
  BUILTIN_PROVENANCE_SHA256,
  sha256Text,
  validateBuiltinProvenance,
} from "../labs/expedition-lab-runtime.js";
import {
  BUILTIN_ARCHIVE_FIXTURE_SHA256,
  BUILTIN_ARCHIVE_PROVENANCE_SHA256,
  archiveSha256Text,
  validateBuiltinArchiveProvenance,
} from "../labs/archive-lab-runtime.js";
import { loadConfiguredFlightRecorder } from "../labs/flight-recorder-runtime.js";

const EVIDENCE_URLS = Object.freeze({
  expeditionProvenance: "labs/expedition-demonstrator.provenance.json",
  archiveProvenance: "labs/archive-lab-demonstrator.provenance.json",
  recorderConfig: "labs/flight-recorder.config.json",
  recorderDemo: "labs/flight-recorder-demo.fixture.json",
});

const KNOWN_CONTENT_STATES = new Set(["pending", "ready", "refused"]);

export class PlatformEvidenceRefusal extends Error {
  constructor(code, message) {
    super(message);
    this.name = "PlatformEvidenceRefusal";
    this.code = code;
  }
}

function refuse(condition, code, message) {
  if (!condition) throw new PlatformEvidenceRefusal(code, message);
}

function freeze(value) {
  if (value && typeof value === "object" && !Object.isFrozen(value)) {
    Object.values(value).forEach(freeze);
    Object.freeze(value);
  }
  return value;
}

async function fetchText(url, fetchImpl) {
  refuse(typeof fetchImpl === "function", "platform-fetch", "fetch is unavailable");
  const response = await fetchImpl(url, { cache: "no-store" });
  refuse(response?.ok, "platform-fetch", `evidence request failed (${response?.status ?? "no response"})`);
  return { text: await response.text(), url: response.url || String(url) };
}

function parseJson(text, at) {
  try {
    return JSON.parse(text);
  } catch {
    throw new PlatformEvidenceRefusal("platform-json", `${at} is not valid JSON`);
  }
}

async function loadExpeditionProvenance(baseUrl, fetchImpl) {
  const response = await fetchText(new URL(EVIDENCE_URLS.expeditionProvenance, baseUrl), fetchImpl);
  const digest = await sha256Text(response.text);
  const provenance = parseJson(response.text, "expedition provenance");
  validateBuiltinProvenance(provenance, digest);
  refuse(
    provenance.artifact.sha256 === BUILTIN_FIXTURE_SHA256,
    "platform-expedition-artifact",
    "expedition provenance names a different table",
  );
  return freeze({
    id: "expedition",
    state: "ready",
    source: "pinned-provenance-manifest",
    provenanceSha256: BUILTIN_PROVENANCE_SHA256,
    artifactSha256: provenance.artifact.sha256,
    sourceCommit: provenance.source_repository_commit,
    states: provenance.lean_gates.states,
    actions: provenance.lean_gates.actions,
    transitions: provenance.lean_gates.transitions,
    acceptingRows: provenance.lean_gates.accepting_rows,
    refusingRows: provenance.lean_gates.refusing_rows,
    fictionStatus: provenance.boundary.fiction_status,
    canonPromotion: provenance.boundary.canon_promotion,
    assetMinting: provenance.boundary.asset_minting,
    settlement: provenance.boundary.settlement,
  });
}

async function loadArchiveProvenance(baseUrl, fetchImpl) {
  const response = await fetchText(new URL(EVIDENCE_URLS.archiveProvenance, baseUrl), fetchImpl);
  const digest = await archiveSha256Text(response.text);
  const provenance = parseJson(response.text, "archive provenance");
  validateBuiltinArchiveProvenance(provenance, digest);
  refuse(
    provenance.artifact.sha256 === BUILTIN_ARCHIVE_FIXTURE_SHA256,
    "platform-archive-artifact",
    "archive provenance names a different table",
  );
  return freeze({
    id: "archive",
    state: "ready",
    source: "pinned-provenance-manifest",
    provenanceSha256: BUILTIN_ARCHIVE_PROVENANCE_SHA256,
    artifactSha256: provenance.artifact.sha256,
    sourceCommit: provenance.source_repository_commit,
    states: provenance.lean_gates.states,
    actions: provenance.lean_gates.actions,
    transitions: provenance.lean_gates.transitions,
    acceptingRows: provenance.lean_gates.accepting_rows,
    refusingRows: provenance.lean_gates.refusing_rows,
    terminalStates: provenance.lean_gates.terminal_states,
    winningPlans: provenance.lean_gates.winning_plans,
    fictionStatus: provenance.boundary.fiction_status,
    canonPromotion: provenance.boundary.canon_promotion,
    assetMinting: provenance.boundary.asset_minting,
    rewardSettlement: provenance.boundary.reward_settlement,
  });
}

async function loadRecorder(baseUrl, fetchImpl) {
  const recorder = await loadConfiguredFlightRecorder(
    new URL(EVIDENCE_URLS.recorderConfig, baseUrl),
    new URL(EVIDENCE_URLS.recorderDemo, baseUrl),
    { fetchImpl },
  );
  return freeze({
    id: "recorder",
    state: "ready",
    source: recorder.source.kind,
    sourceLabel: recorder.source.label ?? null,
    sourceSha256: recorder.source.sha256 ?? null,
    authorityId: recorder.status.authorityId,
    transitions: recorder.transitions.length,
    reportedTransitionCount: recorder.status.head?.transitionCount ?? 0,
    windowStart: recorder.windowStart,
    windowEnd: recorder.windowEnd,
    fullHistory: recorder.hasFullHistory,
    headDigest: recorder.status.head?.headDigest ?? null,
    consensusFinality: recorder.status.consensusFinality,
  });
}

function refusal(id, error) {
  return freeze({
    id,
    state: "refused",
    code: typeof error?.code === "string" ? error.code : "platform-evidence",
    message: error instanceof Error ? error.message : "evidence refused",
  });
}

/**
 * Load only the small, already-pinned provenance manifests and the configured
 * recorder view. The multi-megabyte finite tables remain lazy inside their labs.
 */
export async function loadPlatformEvidence(options = {}) {
  const baseUrl = new URL(options.baseUrl ?? globalThis.location?.href ?? "https://invalid.local/");
  const fetchImpl = options.fetchImpl ?? globalThis.fetch;
  const jobs = [
    ["expedition", loadExpeditionProvenance(baseUrl, fetchImpl)],
    ["archive", loadArchiveProvenance(baseUrl, fetchImpl)],
    ["recorder", loadRecorder(baseUrl, fetchImpl)],
  ];
  const settled = await Promise.all(jobs.map(async ([id, promise]) => {
    try {
      return await promise;
    } catch (error) {
      return refusal(id, error);
    }
  }));
  return freeze(Object.fromEntries(settled.map((entry) => [entry.id, entry])));
}

function grade(code, label, detail, tone) {
  return freeze({ code, label, detail, tone });
}

function evidenceStatus(entry, ready, refusedCopy) {
  if (!entry) return { state: "pending", status: "reading what this build has installed" };
  if (entry.state === "ready") return { state: "ready", status: ready(entry) };
  // ⚠ The code stays: it is the one part of a refusal that can be searched for.
  return { state: "refused", status: `${refusedCopy}: ${entry.code}` };
}

function evidenceGrade(status, readyGrade, refusedLabel) {
  if (status.state === "ready") return readyGrade;
  if (status.state === "refused") {
    return grade("evidence-refused", refusedLabel, status.status, "red");
  }
  return grade(
    "evidence-pending",
    "STILL READING",
    "Reading what this build has installed. Nothing is graded until it has been read.",
    "dim",
  );
}

/**
 * THE REPLAY'S GRADE, WHICH IS NOT ONE GRADE.
 *
 * ⚠ This used to be a single `LINKED REPLAY` card reading "…and with the head
 * the node reported" — emitted identically whether the transitions came off a
 * live authority or off `labs/flight-recorder-demo.fixture.json`, whose digests
 * are `aaaa…`/`1111…` and whose head no node has ever reported. The shipped
 * `labs/flight-recorder.config.json` is `mode: "demo"`, so that sentence was
 * false on every load of the deployed page: it credited an answer to an organ
 * that never spoke.
 *
 * A pinned rehearsal and a live redacted view are DIFFERENT EVIDENCE, so they
 * get different labels. Neither is finality, and both say so — the linked-ness
 * of a digest chain is a property of the chain, not of any quorum.
 */
function recorderGrade(entry) {
  if (entry?.source === "live-api") {
    return grade(
      "linked-replay",
      "LINKED REPLAY",
      "Every link on screen agrees with the next one, and with the head the authority's node reported. That is not proof the network settled any of it.",
      "blue",
    );
  }
  const label = typeof entry?.sourceLabel === "string" && entry.sourceLabel.length > 0
    ? ` (${entry.sourceLabel})`
    : "";
  return grade(
    "linked-rehearsal",
    "LINKED REHEARSAL",
    `Every link agrees with the next one inside a byte-pinned rehearsal fixture${label}. No node reported this head and no ship made these transitions, so it is not proof the network settled any of it either.`,
    "amber",
  );
}

/**
 * THE JUDGED RUN'S OWN GRADE — the one the register was missing.
 *
 * A practice run is drawn and scored in this browser and grants nothing; that is
 * `NO RUN RECEIPT` below and it is true forever. A JUDGED run is a different
 * object: the node re-derives a curator-committed instance and scores it with
 * the Lean feedback oracle, and this browser never classifies a guess
 * (`src/judged-session.js`). Folding both into one "browser run" row hid the
 * stronger evidence behind the weaker caveat.
 *
 * ⚠ EVERY BRANCH IS MEASURED. `custody` is signer-detected and route-answered;
 * `session` is a document the node served. Nothing here asserts a wall this file
 * believes in, and with nothing measured yet the row reads as unread rather than
 * as an absence.
 */
function judgedState(judged) {
  const custody = judged?.custody ?? null;
  if (!custody) return "pending";
  if (judged?.session?.state === "ready") return "ready";
  return custody.canPlay ? "reachable" : "blocked";
}

function judgedGrade(judged) {
  const custody = judged?.custody ?? null;
  if (!custody) {
    return grade(
      "judged-unread",
      "STILL READING",
      "Nothing has been asked about judged play yet, so nothing is claimed about it in either direction.",
      "dim",
    );
  }
  const settleCode = custody.settleBlocker?.code ?? "settle-blocked";
  if (judged?.session?.state === "ready") {
    return grade(
      "judged-unsettled",
      "NODE-JUDGED, UNSETTLED",
      `The node scored this run against a slot the curator committed to before it opened — this browser classified nothing. It still has not settled, and the reason has a name: ${settleCode}.`,
      "amber",
    );
  }
  if (custody.canPlay) {
    return grade(
      "judged-playable",
      "JUDGED RUN REACHABLE",
      `The session route answered this origin and your signer is installed, so a judged run can be opened here and the node will score it. Settling is a separate act and is refused: ${settleCode}.`,
      "amber",
    );
  }
  const blocker = custody.blocker ?? null;
  return grade(
    "judged-unavailable",
    "NO JUDGED RUN",
    `${blocker?.what ?? "Judged play is not reachable from this terminal."} (${blocker?.code ?? "judged-unavailable"})`,
    "dim",
  );
}

function contentGrade(content) {
  if (content.state === "ready") {
    return grade(
      "signed-content",
      "SIGNED BY THE CURATOR",
      `The curator's signature on manifest revision ${content.epoch}.${content.counter} checks out. That vouches for the rules, not for any run you play.`,
      "mint",
    );
  }
  if (content.state === "refused") {
    return grade("content-refused", "RULES REFUSED", "The rules did not check out here, so no drill opens. This page will not make up a game to fill the gap.", "red");
  }
  return grade("content-pending", "CHECKING THE MANIFEST", "This terminal is still checking the curator's signature. Nothing is claimed until it is done.", "dim");
}

function surface(id, eyebrow, title, copy, href, cta, state, evidenceGrade) {
  return freeze({ id, eyebrow, title, copy, href, cta, state, grade: evidenceGrade });
}

/**
 * Build the one honest platform view from independently graded evidence.
 *
 * `judged` is the MEASURED judged-play state (`judgedCustody` + the session
 * document the node served), or `null` when this page has not asked yet. It is
 * never defaulted to an absence: "we have not looked" and "there is nothing" are
 * different answers and the register renders them differently.
 */
export function buildPlatformModel({ contentAuthority, evidence = {}, judged = null }) {
  refuse(
    contentAuthority && KNOWN_CONTENT_STATES.has(contentAuthority.state),
    "platform-content",
    "content authority state is invalid",
  );
  const content = freeze({ ...contentAuthority });
  const expedition = evidenceStatus(
    evidence.expedition,
    (entry) => `${entry.states} states · ${entry.transitions} explicit rows`,
    "provenance refused",
  );
  const archive = evidenceStatus(
    evidence.archive,
    (entry) => `${entry.states} states · ${entry.transitions} evidence rows`,
    "provenance refused",
  );
  const recorder = evidenceStatus(
    evidence.recorder,
    (entry) => `${entry.source === "live-api" ? "live redacted view" : "demo rehearsal"} · ${entry.transitions}/${entry.reportedTransitionCount} linked`,
    "replay refused",
  );
  const missionCount = content.state === "ready" ? content.missionCount : 0;

  const surfaces = [
    surface(
      "daily",
      "WATCH CYCLE",
      "Field drills",
      // ⚠ THIS COPY USED TO SAY "A run stays in this browser and settles
      // nothing", and the first half of that was FALSE. A PRACTICE run stays
      // here; a JUDGED run is opened on the node, which re-derives the
      // curator-committed instance and scores it — the best thing on this page,
      // hidden behind a caveat that described only the weaker branch. Both
      // clauses below are unconditional facts about what the two modes ARE;
      // whether judged play is reachable right now is measured, and lives in the
      // judged panel and the `judged` register row rather than being asserted
      // here.
      content.state === "ready"
        ? `${missionCount} drill${missionCount === 1 ? " is" : "s are"} open, on rules the curator signed. A practice run stays in this browser and settles nothing; a judged run leaves it, and the node scores it against a slot the curator committed to in advance.`
        : content.state === "refused" ? "The board is shut: the rules did not check out here." : "Checking the curator’s signature before anything opens.",
      "#missions",
      "Open daily board",
      content.state,
      contentGrade(content),
    ),
    surface(
      "expedition",
      "BELOW-DECK LAB",
      "Crew expedition",
      expedition.state === "ready"
        ? `${expedition.status}. The whole table runs in your browser; it settles nothing and promotes nothing into the record.`
        : expedition.status,
      "./labs/expedition-lab.html",
      "Muster a crew",
      expedition.state,
      evidenceGrade(
        expedition,
        grade("pinned-provenance", "PINNED PROVENANCE", "The bytes on disk match the digests this build was compiled against. The full table is checked inside the lab, not out here.", "amber"),
        "PROVENANCE REFUSED",
      ),
    ),
    surface(
      "archive",
      "FIELD ARCHIVE",
      "Evidence intake",
      archive.state === "ready"
        ? `${archive.status}. One research plan, beta only — and only the curator can promote what comes out of it.`
        : archive.status,
      "./labs/archive-lab.html",
      "Open archive lab",
      archive.state,
      evidenceGrade(
        archive,
        grade("pinned-provenance", "PINNED PROVENANCE", "The archive’s manifest is pinned byte for byte. That is all it does: it settles nothing and promotes nothing.", "amber"),
        "PROVENANCE REFUSED",
      ),
    ),
    surface(
      "recorder",
      "PUBLIC WAKE",
      "Flight Recorder",
      recorder.state === "ready"
        ? `${recorder.status}. Every link is checked against the next. That is not the same as the network agreeing it is final, and this does not claim it is.`
        : recorder.status,
      "./labs/flight-recorder.html",
      "Replay the wake",
      recorder.state,
      evidenceGrade(recorder, recorderGrade(evidence.recorder), "REPLAY REFUSED"),
    ),
    surface(
      "crew",
      "CREW MUSTER",
      "Expedition roster",
      "The roles live inside the expedition lab. Nothing here keeps an officer, and nothing here writes a crew receipt — which is not the same as this terminal remembering nothing about you.",
      "#crew",
      "Inspect crew systems",
      "local",
      // ⚠ THE SECOND SENTENCE IS NEW AND IT IS THE HONEST HALF. The first is
      // true and stays: there is no officer profile and no crew receipt
      // anywhere outside Lean — `OfficerLogbook.lean` and `CrewFieldMission*`
      // carry no route, no store and no client. But a player who read only that
      // would conclude the node holds nothing of theirs, and it holds several
      // things, all keyed by player key and all durable:
      // `GalleyMaintenanceDailyRuntime.lean` inserts the actor into
      // `publicPlayers` and then REFUSES a second shift from that key; the
      // judged Signal store is keyed `authority_id || slot_be64 || player_key`
      // (`persist/src/poa_signal_session.rs`) and survives restarts; Canon
      // carries a per-player counter. Understating what is kept is not a
      // conservative error — it is the same wrong direction as overstating it.
      grade(
        "no-profile-receipt",
        "NO PROFILE RECEIPT",
        "A crew choice lives in one local transcript and nowhere else, and no officer profile or crew receipt exists on any surface. What the node does keep is narrower and real: your player key, wherever you have acted — a Galley shift it will not let you take twice, and a judged slot's spent bursts.",
        "dim",
      ),
    ),
    surface(
      "bazaar",
      "LOWER CONCOURSE",
      "Dark Bazaar",
      "You can see what a market here would need. None of the four pieces — inventory, sealed orders, clearing, settlement — is connected yet.",
      "#bazaar",
      "Inspect locked market",
      "locked",
      grade("settlement-locked", "NO SETTLEMENT", "Nothing on this build owns salvage, and nothing on it settles a trade.", "red"),
    ),
    surface(
      "galley",
      "DECK 119 COMMONS",
      "The Galley",
      "The journal anyone can read and the shift you sign come out of one document the node writes. This page draws none of it.",
      "#galley",
      "Enter the Galley",
      "network",
      grade("versioned-node-required", "VERSIONED NODE", "The Galley stays shut unless its node supplies every part — the actions, the view, the events, the receipt, the replay. A missing piece closes the hatch; it is never filled in here.", "blue"),
    ),
  ];

  const register = [
    freeze({ id: "content", name: "Mission rules", state: content.state, grade: contentGrade(content) }),
    freeze({ id: "run", name: "Practice run", state: "local", grade: grade("no-run-receipt", "NO RUN RECEIPT", "A practice run is drawn and scored by this browser, so it grants nothing: no score, no salvage, no rank, and no change to the ship. That can never change — a page cannot be evidence about itself.", "dim") }),
    freeze({ id: "judged", name: "Judged run", state: judgedState(judged), grade: judgedGrade(judged) }),
    freeze({ id: "expedition", name: "Expedition table", state: expedition.state, grade: surfaces[1].grade }),
    freeze({ id: "archive", name: "Archive table", state: archive.state, grade: surfaces[2].grade }),
    freeze({ id: "replay", name: "Event replay", state: recorder.state, grade: surfaces[3].grade }),
  ];

  const crew = freeze({
    roles: ["PATHFINDER", "ENGINEER", "CONTAINMENT", "MEDIC"],
    profile: "unbound",
    custody: "none",
    persistence: "not exposed",
    nodeKeeps: "your player key where you have acted",
    sourceState: expedition.state,
  });
  const bazaar = freeze([
    { label: "Owned salvage", state: "none recorded", ready: false },
    { label: "Private order", state: "not exposed", ready: false },
    { label: "Threshold clearing", state: "not linked", ready: false },
    { label: "Settlement receipt", state: "unavailable", ready: false },
  ]);

  return freeze({
    cycle: "NIGHT WATCH // BETA // NOTHING RESETS AT MIDNIGHT",
    surfaces,
    register,
    crew,
    bazaar,
    recorder: evidence.recorder ?? null,
  });
}

function element(tag, className, text) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}

function gradeNode(item) {
  const node = element("div", `platform-grade platform-grade--${item.grade.tone}`);
  node.dataset.grade = item.grade.code;
  node.append(element("b", "platform-grade__label", item.grade.label), element("span", "platform-grade__detail", item.grade.detail));
  return node;
}

function surfaceCard(item) {
  const article = element("article", `platform-card platform-card--${item.state}`);
  article.dataset.surface = item.id;
  const head = element("div", "platform-card__head");
  head.append(element("p", "panel-label", item.eyebrow), element("span", "platform-card__state", item.state.toUpperCase()));
  const title = element("h3", "platform-card__title", item.title);
  const copy = element("p", "platform-card__copy", item.copy);
  const link = element("a", "platform-card__link", `${item.cta} →`);
  link.href = item.href;
  article.append(head, title, copy, gradeNode(item), link);
  return article;
}

function mountHome(root, model) {
  const heading = element("div", "platform-heading");
  const copy = element("div");
  copy.append(element("p", "panel-label", model.cycle), element("h2", "", "The ship between episodes"));
  heading.append(copy, element("p", "platform-heading__copy", "Play, investigate, archive, and inspect the wake. Each instrument keeps its own evidence grade."));
  const grid = element("div", "platform-grid");
  grid.append(...model.surfaces.map(surfaceCard));
  root.replaceChildren(heading, grid);
}

function mountRegister(root, model) {
  const rows = model.register.map((item) => {
    const row = element("article", `evidence-row evidence-row--${item.state}`);
    row.dataset.evidence = item.id;
    row.append(element("span", "evidence-row__name", item.name), gradeNode(item));
    return row;
  });
  root.replaceChildren(...rows);
}

function mountCrew(root, model) {
  const roster = element("div", "crew-roster");
  roster.append(...model.crew.roles.map((role, index) => {
    const card = element("article", "crew-role");
    card.append(element("span", "crew-role__index", String(index + 1).padStart(2, "0")), element("b", "", role), element("small", "", "demonstrator role"));
    return card;
  }));
  const facts = element("dl", "crew-facts");
  for (const [label, value] of [
    ["Officer profile", model.crew.profile],
    ["Asset custody", model.crew.custody],
    ["Persistent roster", model.crew.persistence],
    // Without this row the three above read as "nothing about you is kept",
    // which is false everywhere else on this terminal.
    ["What the node keeps", model.crew.nodeKeeps],
  ]) {
    const row = element("div");
    row.append(element("dt", "", label), element("dd", "", value));
    facts.append(row);
  }
  root.replaceChildren(roster, facts);
}

function mountBazaar(root, model) {
  root.replaceChildren(...model.bazaar.map((gate) => {
    const row = element("article", "bazaar-gate");
    row.setAttribute("aria-disabled", "true");
    row.append(element("span", "bazaar-gate__glyph", "◇"), element("b", "", gate.label), element("small", "", gate.state));
    return row;
  }));
}

/** Mount all platform projections. No control here settles, signs, or promotes. */
export function mountPlatformTerminal(roots, model) {
  if (roots.home) mountHome(roots.home, model);
  if (roots.register) mountRegister(roots.register, model);
  if (roots.crew) mountCrew(roots.crew, model);
  if (roots.bazaar) mountBazaar(roots.bazaar, model);
}

export { EVIDENCE_URLS };
