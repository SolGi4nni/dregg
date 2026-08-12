import { loadMissionCatalog, missionByGameId } from "/src/mission-catalog.js";
import {
  buildJudgedPanel,
  guessStatementMessage,
  judgedCustody,
  loadJudgedSession,
  mountJudgedPanel,
  openJudgedSession,
  openStatementMessage,
  spendJudgedBurst,
} from "/src/judged-session.js";
import { loadPOAG1 } from "/src/poag1.js";
import { loadSignalDescriptor } from "/src/signal-runtime.js";
import { loadSlotState } from "/src/today-board.js";
import {
  POA_CURATOR_KEY_URL,
  POA_EXPECTED_CONTENT_EPOCH,
  POA_EXPECTED_CURATOR_COUNTER,
} from "/src/trust-config.js";

const root = document.getElementById("judged-panel");
const status = document.getElementById("integration-status");
const encoder = new TextEncoder();
const hex = (bytes) => [...new Uint8Array(bytes)].map((byte) => byte.toString(16).padStart(2, "0")).join("");

let slot = null;
let mission = null;
let descriptor = null;
let session = null;
let custody = null;

function report(phase, detail) {
  document.body.dataset.status = phase;
  status.textContent = detail;
}

async function ephemeralProvider() {
  const keys = await crypto.subtle.generateKey({ name: "Ed25519" }, false, ["sign", "verify"]);
  const playerKeyHex = hex(await crypto.subtle.exportKey("raw", keys.publicKey));
  return Object.freeze({
    async getActiveIdentity() { return { publicKeyHex: playerKeyHex }; },
    async signSignalSession(request) {
      const statement = request.kind === "open"
        ? openStatementMessage({ authorityId: request.authorityId, slot: request.slot, playerKey: playerKeyHex })
        : guessStatementMessage({
          authorityId: request.authorityId,
          slot: request.slot,
          playerKey: playerKeyHex,
          round: request.round,
          guess: request.guess,
        });
      const signatureHex = hex(await crypto.subtle.sign("Ed25519", keys.privateKey, encoder.encode(statement)));
      return { playerKeyHex, signatureHex, statement };
    },
  });
}

function render() {
  const panel = buildJudgedPanel({ slot, custody, session });
  mountJudgedPanel(root, panel, { guessSymbols: descriptor.symbols, onAction: perform });
  document.body.dataset.panelState = panel.state;
  document.body.dataset.rounds = session?.state === "ready" ? String(session.session.roundsUsed) : "0";
}

async function perform(code, guess) {
  report("working", code === "session-open" ? "Signing and opening the judged session…" : "Signing and spending one burst…");
  if (code === "session-open") {
    session = await openJudgedSession({
      provider: window.dregg,
      authorityId: mission.federationId,
      commitment: slot.commitment,
      slot: slot.slot,
      baseUrl: location.href,
    });
  } else if (code === "session-guess") {
    session = await spendJudgedBurst({
      provider: window.dregg,
      authorityId: mission.federationId,
      commitment: slot.commitment,
      slot: slot.slot,
      round: session.session.roundsUsed,
      guess,
      baseUrl: location.href,
    });
  }
  custody = judgedCustody(window.dregg, session);
  render();
  if (session?.state !== "ready") {
    report("fail", `FAIL ${session?.code ?? "session-state"}: ${session?.reason ?? "session did not become ready"}`);
    return;
  }
  if (session.session.roundsUsed > 0) {
    report("pass", `PASS: browser opened the live judged session and the node served round ${session.session.roundsUsed} with LOCKED/DRIFT feedback.`);
  } else {
    report("opened", "OPENED: the live node accepted the browser signature. Choose all three bands and spend a burst.");
  }
}

try {
  const bundle = await loadPOAG1({
    baseUrl: new URL("/artifacts/poag1/", location.origin),
    curatorKeyUrl: new URL(POA_CURATOR_KEY_URL, location.origin),
    expectedContentEpoch: POA_EXPECTED_CONTENT_EPOCH,
    expectedCounter: POA_EXPECTED_CURATOR_COUNTER,
  });
  const missions = await loadMissionCatalog(bundle);
  mission = missionByGameId(missions, "signal-triangulation");
  descriptor = loadSignalDescriptor(bundle.payloads[mission.descriptorPath].json, mission, bundle.contentEpoch);
  const curator = await (await fetch(POA_CURATOR_KEY_URL, { cache: "no-store" })).json();
  slot = await loadSlotState({
    authorityId: mission.federationId,
    curatorPublicKey: curator.curator_pubkey,
    baseUrl: location.href,
  });
  if (slot.state !== "open") throw Object.assign(new Error(slot.reason ?? `slot is ${slot.state}`), { code: slot.code ?? "slot-not-open" });

  window.dregg = await ephemeralProvider();
  const identity = await window.dregg.getActiveIdentity();
  session = await loadJudgedSession({
    authorityId: mission.federationId,
    commitment: slot.commitment,
    playerKey: identity.publicKeyHex,
    baseUrl: location.href,
  });
  custody = judgedCustody(window.dregg, session);
  render();
  report("ready", `READY: signed counter ${bundle.contentEpoch.counter}, verified slot ${slot.slot}, and bound an ephemeral browser player. Open the judged run.`);
} catch (error) {
  report("fail", `FAIL ${error?.code ?? error?.name ?? "integration"}: ${error?.stack ?? error}`);
}
