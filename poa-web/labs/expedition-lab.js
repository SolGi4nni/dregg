import { mountExpeditionLab } from "./expedition-lab-controller.js";
import {
  BUILTIN_FIXTURE_SHA256,
  ExpeditionArtifactRefusal,
  fetchBuiltinExpeditionDescriptor,
} from "./expedition-lab-runtime.js";

export const PINNED_FIXTURE_URL = new URL("./expedition-demonstrator.fixture.json", import.meta.url).href;
export const PINNED_PROVENANCE_URL = new URL("./expedition-demonstrator.provenance.json", import.meta.url).href;

const root = document.querySelector("#expedition-lab");
const sourceStatus = document.querySelector("#descriptor-status");
let controller = null;
let request = 0;

function showFatal(error) {
  const panel = document.createElement("section");
  panel.className = "lab-fatal";
  panel.setAttribute("role", "alert");
  const title = document.createElement("h1");
  title.textContent = "Expedition authority refused";
  const detail = document.createElement("p");
  detail.textContent = `${error.code ?? "expedition-error"}: ${error.message}`;
  const boundary = document.createElement("p");
  boundary.textContent = "No fallback rules, query-selected source, or stale expedition controls were opened.";
  panel.append(title, detail, boundary);
  root.replaceChildren(panel);
}

/** Load only the provenance-pinned built-in fixture. Query overrides are inert. */
export async function loadLab() {
  const activeRequest = ++request;
  root.setAttribute("aria-busy", "true");
  sourceStatus.dataset.state = "loading";
  sourceStatus.textContent = "Checking compiled provenance, source, commit, and exact Lean output pins…";
  try {
    const descriptor = await fetchBuiltinExpeditionDescriptor(PINNED_FIXTURE_URL, PINNED_PROVENANCE_URL);
    if (activeRequest !== request) return null;
    controller?.destroy();
    controller = mountExpeditionLab(root, descriptor, {
      onTranscript: (transcript) => { root.dataset.transcript = transcript; },
    });
    root.setAttribute("aria-busy", "false");
    sourceStatus.dataset.state = "ready";
    sourceStatus.textContent = `${descriptor.states.length} states × ${descriptor.actions.length} actions = ${descriptor.transitions.length} explicit rows. Provenance and output bytes pinned (${BUILTIN_FIXTURE_SHA256.slice(0, 12)}…).`;
    return descriptor;
  } catch (error) {
    if (activeRequest !== request) return null;
    root.setAttribute("aria-busy", "false");
    sourceStatus.dataset.state = "error";
    sourceStatus.textContent = `Refused: ${error.message}`;
    showFatal(error instanceof Error ? error : new ExpeditionArtifactRefusal("expedition-error", String(error)));
    return null;
  }
}

loadLab();
