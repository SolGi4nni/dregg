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
  if (!entry) return { state: "pending", status: "checking installed evidence" };
  if (entry.state === "ready") return { state: "ready", status: ready(entry) };
  return { state: "refused", status: `${refusedCopy}: ${entry.code}` };
}

function evidenceGrade(status, readyGrade, refusedLabel) {
  if (status.state === "ready") return readyGrade;
  if (status.state === "refused") {
    return grade("evidence-refused", refusedLabel, status.status, "red");
  }
  return grade(
    "evidence-pending",
    "EVIDENCE CHECK",
    "Reading the installed evidence source; no grade is asserted yet.",
    "dim",
  );
}

function contentGrade(content) {
  if (content.state === "ready") {
    return grade(
      "signed-content",
      "SIGNED CONTENT",
      `Curator-authenticated POAG1 epoch ${content.epoch}.${content.counter}; this authenticates rules, not a played run.`,
      "mint",
    );
  }
  if (content.state === "refused") {
    return grade("content-refused", "CONTENT REFUSED", "Mission controls are sealed; no browser fallback is available.", "red");
  }
  return grade("content-pending", "AUTHORITY CHECK", "The signed POAG1 content epoch is still being authenticated.", "dim");
}

function surface(id, eyebrow, title, copy, href, cta, state, evidenceGrade) {
  return freeze({ id, eyebrow, title, copy, href, cta, state, grade: evidenceGrade });
}

/** Build the one honest platform view from independently graded evidence. */
export function buildPlatformModel({ contentAuthority, evidence = {} }) {
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
      content.state === "ready"
        ? `${missionCount} authenticated drills are open. Runs remain local and unsettled.`
        : content.state === "refused" ? "The field board is sealed because its signed content did not authenticate." : "Authenticating today’s field board.",
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
        ? `${expedition.status}. A complete local finite-table demonstrator; no canon or settlement authority.`
        : expedition.status,
      "./labs/expedition-lab.html",
      "Muster a crew",
      expedition.state,
      evidenceGrade(
        expedition,
        grade("pinned-provenance", "PINNED PROVENANCE", "Manifest bytes and Lean-emission claims match compiled pins. The full table validates inside the lab.", "amber"),
        "PROVENANCE REFUSED",
      ),
    ),
    surface(
      "archive",
      "FIELD ARCHIVE",
      "Evidence intake",
      archive.state === "ready"
        ? `${archive.status}. One beta-only research plan; promotion remains curator-only.`
        : archive.status,
      "./labs/archive-lab.html",
      "Open archive lab",
      archive.state,
      evidenceGrade(
        archive,
        grade("pinned-provenance", "PINNED PROVENANCE", "The archive provenance manifest is byte-pinned; it does not itself settle or promote a record.", "amber"),
        "PROVENANCE REFUSED",
      ),
    ),
    surface(
      "recorder",
      "PUBLIC WAKE",
      "Flight Recorder",
      recorder.state === "ready"
        ? `${recorder.status}. Digest continuity is checked; consensus finality is explicitly not asserted.`
        : recorder.status,
      "./labs/flight-recorder.html",
      "Replay the wake",
      recorder.state,
      evidenceGrade(
        recorder,
        grade("linked-replay", "LINKED REPLAY", "Every visible predecessor/successor link and the reported head agree. This is not a finality proof.", "blue"),
        "REPLAY REFUSED",
      ),
    ),
    surface(
      "crew",
      "CREW MUSTER",
      "Expedition roster",
      "Roles exist inside the expedition demonstrator. No persistent officer profile or crew receipt exists on this surface.",
      "#crew",
      "Inspect crew systems",
      "local",
      grade("no-profile-receipt", "NO PROFILE RECEIPT", "Crew choices remain local to a demonstrator transcript.", "dim"),
    ),
    surface(
      "bazaar",
      "LOWER CONCOURSE",
      "Dark Bazaar",
      "The market vocabulary is visible. Inventory, sealed orders, clearing, and settlement remain disconnected here.",
      "#bazaar",
      "Inspect locked market",
      "locked",
      grade("settlement-locked", "NO SETTLEMENT", "No DrEX settlement receipt or owned salvage inventory is available to this web build.", "red"),
    ),
    surface(
      "galley",
      "DECK 119 COMMONS",
      "The Galley",
      "The public journal and signed maintenance share one node-authored projection. Actions use opaque expiring tokens, exact turn postcards, and returned receipt evidence.",
      "#galley",
      "Enter the Galley",
      "network",
      grade("versioned-node-required", "VERSIONED NODE", "The Galley fails closed unless its frozen V1 node API supplies every action, projection, event, receipt, and replay summary.", "blue"),
    ),
  ];

  const register = [
    freeze({ id: "content", name: "Mission rules", state: content.state, grade: contentGrade(content) }),
    freeze({ id: "run", name: "Browser run", state: "local", grade: grade("no-run-receipt", "NO RUN RECEIPT", "A local transcript grants no score, ship effect, salvage, rank, or canon status.", "dim") }),
    freeze({ id: "expedition", name: "Expedition table", state: expedition.state, grade: surfaces[1].grade }),
    freeze({ id: "archive", name: "Archive table", state: archive.state, grade: surfaces[2].grade }),
    freeze({ id: "replay", name: "Event replay", state: recorder.state, grade: surfaces[3].grade }),
  ];

  const crew = freeze({
    roles: ["PATHFINDER", "ENGINEER", "CONTAINMENT", "MEDIC"],
    profile: "unbound",
    custody: "none",
    persistence: "not exposed",
    sourceState: expedition.state,
  });
  const bazaar = freeze([
    { label: "Owned salvage", state: "none recorded", ready: false },
    { label: "Private order", state: "not exposed", ready: false },
    { label: "Threshold clearing", state: "not linked", ready: false },
    { label: "Settlement receipt", state: "unavailable", ready: false },
  ]);

  return freeze({
    cycle: "NIGHT WATCH // LOCAL BETA // NO AUTHORITATIVE DAILY RESET",
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
  for (const [label, value] of [["Officer profile", model.crew.profile], ["Asset custody", model.crew.custody], ["Persistent roster", model.crew.persistence]]) {
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
