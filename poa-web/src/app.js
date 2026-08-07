import { ArtifactRefusal, loadPOAG1 } from "./poag1.js";
import { POA_CURATOR_KEY_URL, POA_EXPECTED_CONTENT_EPOCH, POA_EXPECTED_CURATOR_COUNTER } from "./trust-config.js";
import {
  canonicalReplay,
  createPracticeRun,
  loadSignalDescriptor,
  submitPracticeGuess,
} from "./signal-runtime.js";
import { finiteTableAuthority, loadMissionCatalog, missionByGameId } from "./mission-catalog.js";
import { loadRelayRepairDescriptor } from "./relay-runtime.js";
import { loadSalvageLockDescriptor, salvagePracticeOracle } from "./salvage-runtime.js";
import { INSTALLED_GAME_IDS, launchCatalogMission } from "./mission-launcher.js";
import { buildRack, mountGameRack } from "./game-rack.js";
import { buildRunSummary, mountRunSummary, runOutcome } from "./run-summary.js";
import { readRackResults, recordRackResult } from "./rack-results.js";
import { buildTodayBoard, loadSlotState, mountTodayBoard } from "./today-board.js";
import {
  buildJudgedPanel,
  judgedCustody,
  loadJudgedSession,
  mountJudgedPanel,
} from "./judged-session.js";
import {
  buildCrateOpenAction,
  buildStationPanel,
  loadStationState,
  mountCrateOpenAction,
  mountStationPanel,
  openSalvageCrate,
} from "./station-panel.js";
import { buildRecordsModel, loadRecordsState, mountRecords } from "./records-view.js";
import { buildGalleyStatus, mountGalleyStatus, probeGalleyStatus } from "./galley-status.js";
import { mountDreggAdmissionPanel } from "./dregg-admission-panel.js";
import { getWalletStandardRegistry } from "./wallet-standard-registry.js";
import { mountGalley } from "./galley-controller.js";
import { createGalleyTransport } from "./galley-runtime.js";
import { resolveTerminalRoute } from "./terminal-route.js";
import {
  buildPlatformModel,
  loadPlatformEvidence,
  mountPlatformTerminal,
} from "./platform-terminal.js";

const byId = (id) => document.getElementById(id);
const state = {
  bundle: null,
  missions: Object.freeze([]),
  games: Object.freeze([]),
  cards: Object.freeze([]),
  results: Object.freeze({}),
  activeGame: null,
  finiteController: null,
  signal: null,
  run: null,
  draft: [],
  galleyController: null,
  platformEvidence: Object.freeze({}),
  slot: null,
  station: null,
  /**
   * What custody this page has for JUDGED Signal, and the judged session itself.
   *
   * ⚑ THE SIGNER WALL FELL (2026-08-07). `window.dregg.signSignalSession` now
   * signs exactly the two documented session statements with the player key —
   * scoped and schema-pinned, deliberately not a signing oracle. What is left
   * is node-side: the session routes are in `protected_routes` and this origin
   * holds no bearer, so the POST lands 401 and `judgedCustody` — which takes the
   * MEASURED session result, not a belief — reports `canPlay: false` naming that
   * wall. The panel renders the action DISABLED against a measurement, and
   * enables itself the day the route answers, with no change here.
   */
  judgedCustody: null,
  judgedSession: null,
  /**
   * The crew identity the crate open is authorized under, or `null`.
   *
   * ⚠ IT IS `null` AND THIS PAGE WILL NOT INVENT ONE. Opening the crate is an
   * authorized act against the curator's authored roster, and this terminal
   * binds no crew key — so the control renders DISABLED with that reason,
   * rather than being hidden or fed a key made up here. The day a crew binding
   * lands, this is what it fills, and nothing else about the action changes.
   */
  crew: null,
  /** The last crate opening this terminal attempted, as a STATE. */
  crateOpen: null,
  records: null,
  galleyProbe: null,
  galleyView: null,
  contentAuthority: Object.freeze({ state: "pending" }),
};

/**
 * The only rung a run in this browser can honestly reach.
 *
 * Nothing on this page submits a transcript anywhere: there is no submit call,
 * no node round-trip, and `createJudgedRun` is never reached because the app
 * hands every controller a practice session. So `practice` is the whole map. If
 * a judged path ever lands, this refuses loudly instead of quietly picking the
 * nearest-looking rung, which is how a rehearsal would start reading as a result.
 */
const STATUS_BY_MODE = Object.freeze({ practice: "practice" });

function localStore() {
  try { return globalThis.localStorage ?? null; } catch { return null; }
}

const deckCopy = {
  118: ["DECK 118", "Cartography shell: no signed field record is attached to this hotspot."],
  119: ["DECK 119", "Cartography shell: no signed field record is attached to this hotspot."],
  121: ["DECK 121", "Mission presentation location. POAG1 does not currently declare deck placement."],
  123: ["DECK 123", "Cartography shell: future expeditions may attach exact receipt-backed records here."],
  125: ["DECK 125", "Unsurveyed display region. No beta artifact is present."],
  126: ["DECK 126", "Unsurveyed display region. No beta artifact is present."],
};

function route() {
  const known = [...document.querySelectorAll("[data-view]")].map((node) => node.dataset.view);
  const active = resolveTerminalRoute(location, known);
  document.querySelectorAll("[data-view]").forEach((view) => view.classList.toggle("active", view.dataset.view === active));
  document.querySelectorAll("[data-route]").forEach((link) => link.classList.toggle("active", link.dataset.route === active));
  document.title = `${active === "overview" ? "KHOVOKHI" : active.toUpperCase()} // Path of Angels`;
  document.querySelector("main")?.scrollTo({ top: 0 });
}

function initializeChrome() {
  window.addEventListener("hashchange", route);
  route();
  document.querySelectorAll("[data-goto]").forEach((button) => button.addEventListener("click", () => { location.hash = button.dataset.goto; }));
  document.querySelectorAll("[data-deck]").forEach((button) => button.addEventListener("click", () => {
    const [heading, copy] = deckCopy[button.dataset.deck] ?? ["UNMAPPED", "No record available."];
    byId("deck-readout").innerHTML = `<b>${heading}</b><span>${copy}</span>`;
    document.querySelectorAll("[data-deck]").forEach((node) => node.classList.toggle("active", node === button));
  }));
  const dialog = byId("curator-dialog");
  byId("curator-open").addEventListener("click", () => dialog.showModal());
  setInterval(() => { byId("ship-clock").textContent = `${new Date().toISOString().slice(11, 19)} UTC`; }, 1000);
  byId("ship-clock").textContent = `${new Date().toISOString().slice(11, 19)} UTC`;

  renderMeters([
    ["INTEL", 0, "#d6e779"], ["SUPPLIES", 0, "#dcac62"],
    ["COHESION", 0, "#9bd8bf"], ["INFLUENCE", 0, "#a9cbd6"],
  ]);

  byId("signal-clear").addEventListener("click", clearDraft);
  byId("signal-submit").addEventListener("click", submitDraft);
  byId("stage-back").addEventListener("click", closeStage);
}

/** Put the rack back in front of the player and stop the drill talking. */
function closeStage() {
  byId("mission-stage").hidden = true;
  byId("run-summary-root").hidden = true;
  byId("run-summary-root").replaceChildren();
  state.finiteController?.destroy();
  state.finiteController = null;
  state.activeGame = null;
  renderRack();
  byId("mission-rack").querySelector("[data-open-game]")?.focus();
}

function renderGalleyStanding() {
  const root = byId("galley-standing");
  if (!root) return;
  mountGalleyStatus(root, buildGalleyStatus({ probe: state.galleyProbe, view: state.galleyView }));
}

/**
 * Ask the Galley status route with no actor header at all.
 *
 * This is the only thing a visitor without a Dregg identity can learn about the
 * organ, and it is worth learning: a node that refuses with its own
 * actor-required code has said the Galley is mounted and answering. The terminal
 * below supersedes this the moment it obtains a real personalized document.
 */
async function initializeGalleyStanding() {
  renderGalleyStanding();
  state.galleyProbe = await probeGalleyStatus({ baseUrl: location.href });
  renderGalleyStanding();
}

function initializeGalley() {
  const root = byId("galley-root");
  if (!root) return;
  try {
    state.galleyController = mountGalley(root, {
      transport: createGalleyTransport({ origin: location.origin }),
      dreggProvider: window.dregg ?? null,
      onView: (view) => {
        state.galleyView = view;
        renderGalleyStanding();
      },
    });
  } catch (error) {
    console.error("PoA Galley unavailable", error);
    root.dataset.state = "unavailable";
    const fallback = root.querySelector("p:last-child");
    if (fallback) fallback.textContent = "The versioned Galley node instrument is unavailable. No browser-authored game fallback was opened.";
  }
}

function initializeDreggAdmission() {
  const root = byId("dregg-admission-root");
  if (!root) return;
  try {
    mountDreggAdmissionPanel(root, {
      walletsRegistry: getWalletStandardRegistry(window),
      origin: location.origin,
    });
  } catch (error) {
    console.error("PoA wallet admission unavailable", error);
    root.dataset.state = "unavailable";
    const fallback = root.querySelector("[role='status']");
    if (fallback) fallback.lastElementChild.textContent =
      "Wallet Standard discovery or the same-origin PoA node is unavailable. No access was granted.";
  }
}

function renderMeters(meters) {
  const max = Math.max(1, ...meters.map(([, value]) => value));
  byId("world-meters").replaceChildren(...meters.map(([label, value]) => {
    const row = document.createElement("div");
    row.className = `meter meter-${label.toLowerCase()}`;
    row.innerHTML = `<span>${label}</span><progress value="${value}" max="${max}">${value}</progress><output>+${value}</output>`;
    return row;
  }));
}

function markAuthority(bundle) {
  const short = bundle.manifestDigest.slice(7, 23);
  byId("artifact-lamp").classList.add("ok");
  byId("artifact-status").textContent = "LEAN AUTHORITY READY";
  byId("artifact-detail").textContent = "The control below dispatches only transitions present in the pinned Lean-emitted table.";
  byId("artifact-pin").textContent = `POAG1 / ${short}`;
  byId("footer-authority").textContent = `POAG1 ${short} // CONTENT EPOCH ${bundle.contentEpoch.contentEpoch}.${bundle.contentEpoch.counter}`;
  byId("rules-authority").textContent = `POAG1 ${short}`;
  byId("curator-artifact").value = bundle.manifestDigest;
  state.contentAuthority = Object.freeze({
    state: "ready",
    manifestDigest: bundle.manifestDigest,
    epoch: bundle.contentEpoch.contentEpoch,
    counter: bundle.contentEpoch.counter,
    missionCount: state.missions.length,
  });
  renderPlatform();
}

function sealAuthority(error) {
  console.error(error);
  byId("artifact-lamp").classList.add("bad");
  byId("artifact-status").textContent = "MISSION AUTHORITY SEALED";
  byId("fatal-artifact").hidden = false;
  byId("fatal-detail").textContent = error instanceof ArtifactRefusal ? `${error.code}: ${error.message}` : "The mission bundle was refused.";
  byId("signal-instruction").textContent = "No controls are available: the mission rules did not authenticate.";
  byId("artifact-detail").textContent = "The game remains sealed. No browser-authored fallback exists.";
  byId("artifact-pin").textContent = "POAG1 / REFUSED";
  byId("rules-authority").textContent = "refused";
  byId("footer-authority").textContent = "Mission authority refused";
  state.finiteController?.destroy();
  state.finiteController = null;
  byId("finite-game").hidden = true;
  byId("mission-stage").hidden = true;
  disableSignal();
  state.contentAuthority = Object.freeze({
    state: "refused",
    reason: error instanceof ArtifactRefusal ? error.code : "mission-authority",
  });
  // The rack still renders: with no authenticated catalog every slot is sealed,
  // which is the honest picture. A blank board would have hidden the refusal.
  state.missions = Object.freeze([]);
  renderRack();
  renderPlatform();
  renderToday();
  // With no authenticated catalog there is no federation to ask about, so the
  // station and the records land as sealed views that SAY that, rather than
  // staying on a loading line that will never resolve.
  state.station = Object.freeze({ state: "unreachable", code: "station-authority", reason: "No authenticated catalog names a federation to ask about" });
  state.records = Object.freeze({ state: "unreachable", code: "records-authority", reason: "No authenticated catalog names a federation to ask about" });
  renderStation();
  renderRecords();
}

function renderPlatform() {
  const model = buildPlatformModel({
    contentAuthority: state.contentAuthority,
    evidence: state.platformEvidence,
  });
  mountPlatformTerminal({
    home: byId("platform-terminal"),
    register: byId("evidence-register"),
    crew: byId("crew-systems"),
    bazaar: byId("bazaar-gates"),
  }, model);
}

async function initializePlatformEvidence() {
  renderPlatform();
  renderToday();
  state.platformEvidence = await loadPlatformEvidence({ baseUrl: location.href });
  renderPlatform();
  renderToday();
}

function renderToday() {
  mountTodayBoard(byId("today-board"), buildTodayBoard({
    slot: state.slot,
    recorder: state.platformEvidence.recorder ?? null,
    contentAuthority: state.contentAuthority,
    cards: state.cards,
    station: state.station,
  }));
  renderJudged();
}

/**
 * The judged-session panel, mounted beside the board that says whether a slot is
 * open at all.
 *
 * ⚠ It reads `state.slot` — the opening this page ALREADY verified against the
 * pinned curator key — and never re-fetches or re-checks it. One verifier; a
 * second one is a second answer waiting to disagree.
 */
function renderJudged() {
  const root = byId("judged-panel");
  if (!root) return;
  mountJudgedPanel(root, buildJudgedPanel({
    slot: state.slot,
    custody: state.judgedCustody,
    session: state.judgedSession,
  }));
}

/**
 * Ask whether this player has a judged session open, once the slot is verified.
 *
 * Deliberately best-effort and deliberately quiet about failure: the session
 * routes are authenticated and this origin holds no bearer, so on the live
 * deployment this lands as `unauthenticated` and the panel says so in words.
 * That is the honest state, not an error — and it can only ever fail toward
 * "no judged session shown".
 */
async function initializeJudgedSession() {
  state.judgedCustody = judgedCustody(window.dregg ?? null);
  renderJudged();
  if (state.slot?.state !== "open") return;
  let playerKey = null;
  try {
    const identity = await window.dregg?.getActiveIdentity?.();
    if (typeof identity?.publicKeyHex === "string") playerKey = identity.publicKeyHex;
  } catch {
    // A declined or absent identity is the `unbound` panel, not a failure.
  }
  if (!playerKey) return;
  state.judgedSession = await loadJudgedSession({
    authorityId: state.missions[0]?.federationId ?? null,
    commitment: state.slot.commitment,
    playerKey,
    baseUrl: location.href,
  });
  // ⚑ RE-READ CUSTODY AGAINST WHAT THE ROUTE ACTUALLY DID. `canPlay` is not a
  // constant this file believes; it is signer-detected AND route-answered. A
  // 401 keeps it false and names the bearer wall; a served or 404-ing document
  // makes it true and the panel's action live.
  state.judgedCustody = judgedCustody(window.dregg ?? null, state.judgedSession);
  renderJudged();
}

function renderStation() {
  const root = byId("station-panel");
  if (root) mountStationPanel(root, buildStationPanel(state.station));
  renderCrateOpen();
}

/**
 * The salvage crate's one control.
 *
 * The click sends ONE THING — the crew key — and then RE-READS the panel rather
 * than patching the gauges from the reply. Both documents are folds of the same
 * durable open log, so they agree; but the panel a player looks at should be
 * the one the public route serves, not one this page assembled from a write
 * reply. That difference is the whole reason the loop was open.
 */
function renderCrateOpen() {
  const root = byId("crate-open");
  if (!root) return;
  const action = buildCrateOpenAction({ crew: state.crew, open: state.crateOpen });
  mountCrateOpenAction(root, action);
  if (!action.enabled) return;

  const button = root.children?.find?.((node) => node.tagName === "BUTTON")
    ?? root.querySelector?.("button");
  if (!button) return;
  button.addEventListener("click", async () => {
    const [mission] = state.missions;
    if (!mission || !state.crew) return;
    state.crateOpen = Object.freeze({ state: "pending" });
    renderCrateOpen();
    state.crateOpen = await openSalvageCrate({
      authorityId: mission.federationId,
      opener: state.crew.key,
      baseUrl: location.href,
    });
    // The communal panel is re-read from the public route, so what a player
    // sees after opening is what every other player sees.
    state.station = await loadStationState({ authorityId: mission.federationId, baseUrl: location.href });
    renderStation();
    renderToday();
  }, { once: true });
}

function renderRecords() {
  const root = byId("records-live");
  if (root) mountRecords(root, buildRecordsModel(state.records));
}

/**
 * The two organs that need the authority id the SIGNED catalog names.
 *
 * Both are read-only public surfaces and neither can be asked before the content
 * bundle authenticates, because until then this page does not know which
 * federation it is looking at — and asking a federation the catalog did not name
 * would be reading a world nothing here is pinned to.
 */
async function initializeAuthorityOrgans() {
  const [mission] = state.missions;
  if (!mission) return;
  const [station, records] = await Promise.all([
    loadStationState({ authorityId: mission.federationId, baseUrl: location.href }),
    loadRecordsState({ authorityId: mission.federationId, baseUrl: location.href }),
  ]);
  state.station = station;
  state.records = records;
  renderStation();
  renderRecords();
  renderToday();
}

/**
 * Ask the authority whether a judged slot is open.
 *
 * The authority id is the federation the SIGNED catalog names, and the key the
 * opening must be signed under is the one the content bundle is already pinned
 * to — so this asks a question it already knows how to check the answer to. Any
 * failure lands as a sealed tile and the rack stays practice-only; there is no
 * path here that turns a reachable node into a judged run.
 */
async function initializeSlotState() {
  const [mission] = state.missions;
  if (!mission || !state.bundle) return;
  state.slot = await loadSlotState({
    authorityId: mission.federationId,
    curatorPublicKey: state.bundle.contentEpoch.curatorPublicKey,
    baseUrl: location.href,
  });
  renderToday();
}

function disableSignal() {
  byId("signal-submit").disabled = true;
  byId("signal-clear").disabled = true;
  byId("signal-symbols").replaceChildren();
  byId("signal-draft").replaceChildren();
}

function token(symbol, className = "signal-token") {
  const node = document.createElement("span");
  node.className = `${className} signal-color-${symbol.id}`;
  node.textContent = symbol.glyph;
  node.title = symbol.label;
  node.setAttribute("aria-label", symbol.label);
  return node;
}

/**
 * The one place this client draws anything. A practice member is a local,
 * unscored choice out of an emitted family — it is not the Lean derivation and
 * must not become it, because reproducing `HiddenInstance` here would put a
 * second copy of the draw in the browser. Judged runs get their member (or, for
 * an oracle-only game, their answers) from the host and never come through here.
 */
function practiceMember(count) {
  const draw = new Uint32Array(1);
  crypto.getRandomValues(draw);
  return draw[0] % count;
}

function initializeSignal(descriptor) {
  state.signal = descriptor;
  state.run = createPracticeRun(descriptor);
  state.draft = [];
  byId("turn-limit").textContent = ` / ${descriptor.maxTurns} TRANSMISSIONS`;
  byId("signal-instruction").textContent = `Assemble ${descriptor.codeLength} carrier bands. Feedback is looked up from the authenticated mission table; the browser does not score it. PRACTICE run: this client picked its own code out of the emitted rulebook, nothing here is scored, and a judged run would learn nothing about its code at all.`;
  byId("signal-symbols").replaceChildren(...descriptor.symbols.map((symbol) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = `signal-choice signal-color-${symbol.id}`;
    button.textContent = `${symbol.glyph} ${symbol.label}`;
    button.addEventListener("click", () => appendSymbol(symbol.id));
    return button;
  }));
  byId("signal-clear").disabled = false;
  byId("signal-receipt").hidden = true;
  renderSignal();
}

function presentMission(mission, card) {
  byId("mission-title").textContent = card?.name ?? mission.title;
  byId("mission-watch-copy").textContent = card?.flavor ?? "";
  document.querySelectorAll("[data-game]").forEach((node) => {
    node.classList.toggle("active", node.dataset.game === mission.gameId);
  });
  const nonzero = ["intel", "supplies", "cohesion", "influence", "score"].filter((key) => mission.reward[key] !== 0);
  byId("mission-contribution").textContent = nonzero.length ? `preview: ${nonzero.join(" / ")}` : "preview: none";
  byId("curator-discovery").value = `mission:${mission.betaArtifact.mission_id} artifact:${mission.betaArtifact.artifact_id}`;
  byId("curator-contribution").value = [
    "UNSETTLED LEAN PREVIEW — NOT WORLD STATE",
    ...["intel", "supplies", "cohesion", "influence", "score"].map((key) => `${key}: ${mission.reward[key]}`),
    `relics: [${mission.reward.relics.join(", ")}]`,
  ].join("\n");
  renderMeters([
    ["INTEL", mission.reward.intel, "#d6e779"],
    ["SUPPLIES", mission.reward.supplies, "#dcac62"],
    ["COHESION", mission.reward.cohesion, "#9bd8bf"],
    ["INFLUENCE", mission.reward.influence, "#a9cbd6"],
  ]);
  byId("world-preview-note").textContent = `Lean-emitted solved-run preview for mission ${mission.missionId}; preview sequence ${mission.previewWorld.sequence}. This is not current ship state and grants nothing.`;
}

/**
 * One rack, rebuilt from evidence every time: the signed catalog decides what is
 * enrolled, the launcher's dispatch table decides what is installed, and this
 * browser's own note decides what a card can say about your last run. No card is
 * assembled by hand, so a new game cannot acquire a special one.
 */
function renderRack() {
  try {
    state.cards = buildRack({
      missions: state.missions,
      installed: INSTALLED_GAME_IDS,
      results: state.results,
    });
  } catch (error) {
    console.error("PoA rack refused", error);
    state.cards = Object.freeze([]);
  }
  mountGameRack(byId("mission-rack"), state.cards, { onOpen: selectMission });
}

function cardFor(gameId) {
  return state.cards.find((card) => card.gameId === gameId) ?? null;
}

/**
 * The one end-of-run screen. Every game reaches it through here, with the same
 * record, so none of them can grow its own idea of what "finished" looks like.
 */
function finishRun(gameId, { mode, outcome, actions, actionLimit, transcript }) {
  const card = cardFor(gameId);
  if (!card) return;
  const status = STATUS_BY_MODE[mode];
  if (!status) {
    console.error(new ArtifactRefusal(
      "run-status-unmapped",
      `this terminal has no path that submits a ${mode} run, so it cannot name a ladder rung for one`,
    ));
    return;
  }
  state.results = recordRackResult(localStore(), gameId, { status, outcome, actions });
  const root = byId("run-summary-root");
  root.hidden = false;
  mountRunSummary(root, buildRunSummary({ card, status, outcome, actions, actionLimit, transcript }), {
    onAgain: () => replayActive(),
    onRack: () => closeStage(),
  });
}

function replayActive() {
  const gameId = state.activeGame;
  byId("run-summary-root").hidden = true;
  byId("run-summary-root").replaceChildren();
  if (!gameId) return;
  if (gameId === "signal-triangulation") {
    initializeSignal(state.signal);
    return;
  }
  state.finiteController?.reset();
}

/**
 * A practice session for a finite-table game: which member of the emitted family
 * this rehearsal plays, and — for an oracle-only game — the local oracle that
 * answers its own questions. Both are unscored by construction, and `mode` puts
 * that in the transcript so a rehearsal cannot be presented as a result.
 */
function practiceSession(gameId, descriptor) {
  if (gameId === "relay-repair") {
    return { mode: "practice", member: practiceMember(descriptor.instance.modulus) };
  }
  if (gameId === "salvage-lock") {
    const member = practiceMember(descriptor.instance.practice.boards.length);
    return { mode: "practice", member, oracle: salvagePracticeOracle(descriptor, member) };
  }
  return undefined;
}

/** Read a finished run through its shape and put it on the one end screen. */
function reportRun(gameId, descriptor, run) {
  const card = cardFor(gameId);
  if (!card) return;
  let reading;
  try {
    reading = runOutcome(card.shape, run, descriptor);
  } catch (error) {
    console.error("PoA end screen refused", error);
    return;
  }
  if (!reading.over) return;
  finishRun(gameId, { ...reading, transcript: null });
}

function selectMission(gameId) {
  try {
    const mission = missionByGameId(state.missions, gameId);
    const descriptor = state.games.find((candidate) => candidate.gameId === gameId);
    state.finiteController?.destroy();
    state.finiteController = null;
    byId("run-summary-root").hidden = true;
    byId("run-summary-root").replaceChildren();
    byId("mission-stage").hidden = false;
    presentMission(mission, cardFor(gameId));
    const launched = launchCatalogMission({
      mission,
      descriptor,
      signalRoot: byId("signal-game"),
      finiteRoot: byId("finite-game"),
      launchSignal: initializeSignal,
      callbacks: {
        session: practiceSession(gameId, descriptor),
        onTranscript: (transcript, run) => reportRun(gameId, descriptor, run),
        onReset: () => {
          byId("run-summary-root").hidden = true;
          byId("run-summary-root").replaceChildren();
        },
      },
    });
    state.activeGame = launched.gameId;
    state.finiteController = launched.controller;
    byId("mission-stage").scrollIntoView({ block: "start" });
  } catch (error) {
    sealAuthority(error);
  }
}

function appendSymbol(symbolId) {
  if (!state.signal || state.run.solved || state.run.exhausted || state.draft.length >= state.signal.codeLength) return;
  state.draft = [...state.draft, symbolId];
  renderDraft();
}

function clearDraft() {
  state.draft = [];
  renderDraft();
}

function renderDraft() {
  if (!state.signal) return;
  const nodes = [];
  for (let i = 0; i < state.signal.codeLength; i += 1) {
    const id = state.draft[i];
    if (id === undefined) {
      const slot = document.createElement("span");
      slot.className = "draft-slot";
      slot.textContent = String(i + 1).padStart(2, "0");
      nodes.push(slot);
    } else {
      nodes.push(token(state.signal.symbols.find((symbol) => symbol.id === id)));
    }
  }
  byId("signal-draft").replaceChildren(...nodes);
  byId("signal-submit").disabled = state.draft.length !== state.signal.codeLength || state.run.solved || state.run.exhausted;
}

function submitDraft() {
  if (!state.signal || state.draft.length !== state.signal.codeLength) return;
  try {
    state.run = submitPracticeGuess(state.signal, state.run, state.draft);
    state.draft = [];
    renderSignal();
  } catch (error) {
    sealAuthority(error);
  }
}

function renderSignal() {
  const { signal, run } = state;
  byId("turn-current").textContent = String(run.turns.length);
  const template = byId("history-row-template");
  const rows = run.turns.map((turn, index) => {
    const row = template.content.firstElementChild.cloneNode(true);
    row.querySelector(".history-num").textContent = String(index + 1).padStart(2, "0");
    row.querySelector(".history-sequence").replaceChildren(...turn.guess.map((id) => token(signal.symbols.find((symbol) => symbol.id === id))));
    row.querySelector(".history-result b").textContent = `${turn.exact} LOCKED`;
    row.querySelector(".history-result small").textContent = `${turn.present} DRIFT`;
    return row;
  });
  byId("signal-history").replaceChildren(...rows);
  document.querySelectorAll(".signal-choice").forEach((button) => { button.disabled = run.solved || run.exhausted; });
  byId("signal-clear").disabled = run.solved || run.exhausted;
  renderDraft();
  if (run.solved || run.exhausted) {
    renderTranscript();
    reportRun("signal-triangulation", signal, run);
  }
}

function renderTranscript() {
  const node = byId("signal-receipt");
  const canonical = canonicalReplay(state.run);
  const title = state.run.solved ? "SIGNAL LOCATED" : "FIELD WINDOW CLOSED";
  const mode = state.run.mode === "practice" ? "PRACTICE TRANSCRIPT — NOT SCORED" : "UNSETTLED JUDGED TRANSCRIPT";
  node.innerHTML = `<b>${title} // ${mode}</b><br>${state.run.turns.length} transmissions recorded locally against a code this client chose for itself. No authoritative world state, salvage, or ranking changes until a PoA node validates and settles a judged run.<br><code>${escapeHtml(canonical)}</code>`;
  node.hidden = false;
}

function escapeHtml(value) {
  return value.replace(/[&<>"]/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[char]));
}

async function boot() {
  initializeChrome();
  state.results = readRackResults(localStore());
  // The rack renders BEFORE anything is authenticated: every slot sealed, which
  // is true, and a shape a first-time player can read while the bytes load.
  renderRack();
  renderStation();
  renderRecords();
  initializeGalley();
  const galleyStanding = initializeGalleyStanding();
  initializeDreggAdmission();
  const platformEvidence = initializePlatformEvidence();
  try {
    const bundle = await loadPOAG1({
      baseUrl: new URL("./artifacts/poag1/", location.href),
      curatorKeyUrl: new URL(POA_CURATOR_KEY_URL, location.origin),
      expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
      expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
    });
    state.bundle = bundle;
    const missions = await loadMissionCatalog(bundle);
    const signalMission = missionByGameId(missions, "signal-triangulation");
    const relayMission = missionByGameId(missions, "relay-repair");
    const salvageMission = missionByGameId(missions, "salvage-lock");
    const signal = loadSignalDescriptor(
      bundle.payloads["games/signal-triangulation.json"].json,
      signalMission,
      bundle.contentEpoch,
    );
    const relay = loadRelayRepairDescriptor(
      bundle.payloads[relayMission.descriptorPath].json,
      finiteTableAuthority(relayMission),
    );
    const salvage = loadSalvageLockDescriptor(
      bundle.payloads[salvageMission.descriptorPath].json,
      finiteTableAuthority(salvageMission),
    );
    state.missions = missions;
    state.games = Object.freeze([signal, relay, salvage]);
    markAuthority(bundle);
    // ⚠ No drill auto-opens any more. The first thing a player meets is the rack.
    renderRack();
    renderToday();
    await Promise.all([initializeSlotState(), initializeAuthorityOrgans()]);
    // ⚠ AFTER the slot, never beside it: a judged session is only ever read
    // against a commitment this page has already verified for itself.
    await initializeJudgedSession();
  } catch (error) {
    sealAuthority(error);
  } finally {
    await Promise.all([platformEvidence, galleyStanding]);
    byId("app").setAttribute("aria-busy", "false");
  }
}

boot();
