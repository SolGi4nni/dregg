import { mountFlightRecorder } from "./flight-recorder-controller.js";
import {
  FlightRecorderRefusal,
  loadConfiguredFlightRecorder,
} from "./flight-recorder-runtime.js";

export const FLIGHT_RECORDER_CONFIG_URL = new URL("./flight-recorder.config.json", import.meta.url).href;
export const FLIGHT_RECORDER_DEMO_URL = new URL("./flight-recorder-demo.fixture.json", import.meta.url).href;

const root = document.querySelector("#flight-recorder");
const sourceStatus = document.querySelector("#flight-source-status");
let controller = null;
let request = 0;

function showFatal(error) {
  const panel = document.createElement("section");
  panel.className = "flight-fatal";
  panel.setAttribute("role", "alert");
  const title = document.createElement("h1");
  title.textContent = "The recorder refused this wake";
  const detail = document.createElement("p");
  detail.textContent = `${error.code ?? "recorder-error"}: ${error.message}`;
  const boundary = document.createElement("p");
  boundary.textContent = "No links were repaired, reordered, or filled from a demo. A configured live source fails closed.";
  panel.append(title, detail, boundary);
  root.replaceChildren(panel);
}

export async function loadFlightRecorder() {
  const activeRequest = ++request;
  root.setAttribute("aria-busy", "true");
  sourceStatus.dataset.state = "loading";
  sourceStatus.textContent = "Reading the fixed recorder config and validating its selected source…";
  try {
    const recorder = await loadConfiguredFlightRecorder(FLIGHT_RECORDER_CONFIG_URL, FLIGHT_RECORDER_DEMO_URL);
    if (activeRequest !== request) return null;
    controller?.destroy();
    controller = mountFlightRecorder(root, recorder, { onRefresh: loadFlightRecorder });
    root.setAttribute("aria-busy", "false");
    if (recorder.source.kind === "demo-fixture") {
      sourceStatus.dataset.state = "demo";
      sourceStatus.textContent = `DEMO FALLBACK — ${recorder.source.label}. Bundled rehearsal bytes; no live node queried.`;
    } else {
      sourceStatus.dataset.state = "live";
      sourceStatus.textContent = `LIVE PUBLIC NODE VIEW — ${recorder.transitions.length} linked transition${recorder.transitions.length === 1 ? "" : "s"} ending at the current redacted head.`;
    }
    return recorder;
  } catch (error) {
    if (activeRequest !== request) return null;
    root.setAttribute("aria-busy", "false");
    sourceStatus.dataset.state = "error";
    sourceStatus.textContent = `Refused: ${error.message}`;
    showFatal(error instanceof Error ? error : new FlightRecorderRefusal("recorder-error", String(error)));
    return null;
  }
}

loadFlightRecorder();
