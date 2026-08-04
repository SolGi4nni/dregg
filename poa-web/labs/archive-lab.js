import { mountArchiveLab } from "./archive-lab-controller.js";
import {
  ArchiveLabArtifactRefusal,
  BUILTIN_ARCHIVE_FIXTURE_SHA256,
  fetchBuiltinArchiveLabDescriptor,
} from "./archive-lab-runtime.js";

export const PINNED_ARCHIVE_FIXTURE_URL = new URL("./archive-lab-demonstrator.fixture.json", import.meta.url).href;
export const PINNED_ARCHIVE_PROVENANCE_URL = new URL("./archive-lab-demonstrator.provenance.json", import.meta.url).href;

const root = document.querySelector("#archive-lab");
const sourceStatus = document.querySelector("#descriptor-status");
let controller = null;
let request = 0;

function showFatal(error) {
  const panel = document.createElement("section");
  panel.className = "lab-fatal";
  panel.setAttribute("role", "alert");
  const title = document.createElement("h1");
  title.textContent = "Archive authority refused";
  const detail = document.createElement("p");
  detail.textContent = `${error.code ?? "archive-error"}: ${error.message}`;
  const boundary = document.createElement("p");
  boundary.textContent = "No fallback deduction, query-selected source, or stale research controls were opened.";
  panel.append(title, detail, boundary);
  root.replaceChildren(panel);
}

/** Load only the provenance-pinned built-in fixture. Query overrides are inert. */
export async function loadArchiveLab() {
  const activeRequest = ++request;
  root.setAttribute("aria-busy", "true");
  sourceStatus.dataset.state = "loading";
  sourceStatus.textContent = "Checking provenance, source, commit, and exact Lean output pins…";
  try {
    const descriptor = await fetchBuiltinArchiveLabDescriptor(PINNED_ARCHIVE_FIXTURE_URL, PINNED_ARCHIVE_PROVENANCE_URL);
    if (activeRequest !== request) return null;
    controller?.destroy();
    controller = mountArchiveLab(root, descriptor, {
      onTranscript: (transcript) => { root.dataset.transcript = transcript; },
    });
    root.setAttribute("aria-busy", "false");
    sourceStatus.dataset.state = "ready";
    sourceStatus.textContent = `${descriptor.states.length} states × ${descriptor.actions.length} moves = ${descriptor.transitions.length} explicit rows. Provenance and output bytes pinned (${BUILTIN_ARCHIVE_FIXTURE_SHA256.slice(0, 12)}…).`;
    return descriptor;
  } catch (error) {
    if (activeRequest !== request) return null;
    root.setAttribute("aria-busy", "false");
    sourceStatus.dataset.state = "error";
    sourceStatus.textContent = `Refused: ${error.message}`;
    showFatal(error instanceof Error ? error : new ArchiveLabArtifactRefusal("archive-error", String(error)));
    return null;
  }
}

loadArchiveLab();
