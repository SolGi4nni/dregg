import { ArtifactRefusal, loadPOAG1 } from "./poag1.js";
import { POA_CURATOR_KEY_URL, POA_EXPECTED_CONTENT_EPOCH, POA_EXPECTED_CURATOR_COUNTER } from "./trust-config.js";
import {
  canonicalReplay,
  createSignalRun,
  loadSignalDescriptor,
  submitSignalGuess,
} from "./signal-runtime.js";
import { finiteTableAuthority, loadMissionCatalog, missionByGameId } from "./mission-catalog.js";
import { loadRelayRepairDescriptor } from "./relay-runtime.js";
import { loadSalvageLockDescriptor } from "./salvage-runtime.js";
import { launchCatalogMission } from "./mission-launcher.js";
import { mountDreggAdmissionPanel } from "./dregg-admission-panel.js";
import { getWalletStandardRegistry } from "./wallet-standard-registry.js";
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
  activeGame: null,
  finiteController: null,
  signal: null,
  run: null,
  draft: [],
  platformEvidence: Object.freeze({}),
  contentAuthority: Object.freeze({ state: "pending" }),
};

const missionCopy = Object.freeze({
  "signal-triangulation": "Reconstruct the band sequence using only authenticated outcome rows emitted by Lean.",
  "relay-repair": "Restore a route by dispatching only the authenticated Relay transition table emitted by Lean.",
  "salvage-lock": "Expose plates and clear pairs through the authenticated Salvage transition table emitted by Lean.",
});

const deckCopy = {
  118: ["DECK 118", "Cartography shell: no signed field record is attached to this hotspot."],
  119: ["DECK 119", "Cartography shell: no signed field record is attached to this hotspot."],
  121: ["DECK 121", "Mission presentation location. POAG1 does not currently declare deck placement."],
  123: ["DECK 123", "Cartography shell: future expeditions may attach exact receipt-backed records here."],
  125: ["DECK 125", "Unsurveyed display region. No beta artifact is present."],
  126: ["DECK 126", "Unsurveyed display region. No beta artifact is present."],
};

function route() {
  const requested = location.hash.slice(1) || "overview";
  const known = [...document.querySelectorAll("[data-view]")].map((node) => node.dataset.view);
  const active = known.includes(requested) ? requested : "overview";
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
  byId("mission-selector").replaceChildren();
  state.finiteController?.destroy();
  state.finiteController = null;
  byId("finite-game").hidden = true;
  disableSignal();
  state.contentAuthority = Object.freeze({
    state: "refused",
    reason: error instanceof ArtifactRefusal ? error.code : "mission-authority",
  });
  renderPlatform();
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
  state.platformEvidence = await loadPlatformEvidence({ baseUrl: location.href });
  renderPlatform();
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

function initializeSignal(descriptor) {
  state.signal = descriptor;
  state.run = createSignalRun(descriptor);
  state.draft = [];
  byId("turn-limit").textContent = `/ ${descriptor.maxTurns} TRANSMISSIONS`;
  byId("signal-instruction").textContent = `Assemble ${descriptor.codeLength} carrier bands. Feedback is looked up from the authenticated mission table; the browser does not score it. Transparent beta drill: the target table is public, and no competitive or economic reward is attached to this local transcript.`;
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

function presentMission(mission) {
  byId("mission-title").textContent = mission.title;
  byId("mission-watch-copy").textContent = missionCopy[mission.gameId];
  document.querySelectorAll("[data-mission-game]").forEach((button) => {
    const selected = button.dataset.missionGame === mission.gameId;
    button.classList.toggle("active", selected);
    button.setAttribute("aria-pressed", String(selected));
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

function renderMissionSelector() {
  byId("mission-selector").replaceChildren(...state.missions.map((mission) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "mission-tab";
    button.dataset.missionGame = mission.gameId;
    button.setAttribute("aria-pressed", "false");
    const number = document.createElement("span");
    number.textContent = String(mission.missionId).padStart(2, "0");
    const label = document.createElement("b");
    label.textContent = mission.title;
    const boundary = document.createElement("small");
    boundary.textContent = "LOCAL // UNSETTLED";
    button.append(number, label, boundary);
    button.addEventListener("click", () => selectMission(mission.gameId));
    return button;
  }));
}

function selectMission(gameId) {
  try {
    const mission = missionByGameId(state.missions, gameId);
    const descriptor = state.games.find((candidate) => candidate.gameId === gameId);
    state.finiteController?.destroy();
    state.finiteController = null;
    presentMission(mission);
    const launched = launchCatalogMission({
      mission,
      descriptor,
      signalRoot: byId("signal-game"),
      finiteRoot: byId("finite-game"),
      launchSignal: initializeSignal,
    });
    state.activeGame = launched.gameId;
    state.finiteController = launched.controller;
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
    state.run = submitSignalGuess(state.signal, state.run, state.draft);
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
  if (run.solved || run.exhausted) renderTranscript();
}

function renderTranscript() {
  const node = byId("signal-receipt");
  const canonical = canonicalReplay(state.run);
  const title = state.run.solved ? "SIGNAL LOCATED" : "FIELD WINDOW CLOSED";
  node.innerHTML = `<b>${title} // UNSETTLED TRANSCRIPT</b><br>${state.run.turns.length} transmissions recorded locally. No authoritative world state, salvage, or ranking changes until a PoA node validates and settles this run.<br><code>${escapeHtml(canonical)}</code>`;
  node.hidden = false;
}

function escapeHtml(value) {
  return value.replace(/[&<>"]/g, (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[char]));
}

async function boot() {
  initializeChrome();
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
    renderMissionSelector();
    selectMission("signal-triangulation");
  } catch (error) {
    sealAuthority(error);
  } finally {
    await platformEvidence;
    byId("app").setAttribute("aria-busy", "false");
  }
}

boot();
