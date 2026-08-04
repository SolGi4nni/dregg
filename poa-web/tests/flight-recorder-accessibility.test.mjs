import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("standalone Flight Recorder has a skip target, live source status, and no query/config form", async () => {
  const html = await read("../labs/flight-recorder.html");
  assert.match(html, /class="flight-skip" href="#flight-recorder"/);
  assert.match(html, /id="flight-recorder" tabindex="-1" aria-busy="true"/);
  assert.match(html, /id="flight-source-status"[^>]*role="status"[^>]*aria-live="polite"/);
  assert.match(html, /CONFIGURED SOURCE ONLY/);
  assert.match(html, /Query parameters cannot redirect the recorder/);
  assert.doesNotMatch(html, /<form|<input|name="endpoint"|name="authority"/);
  assert.match(html, /type="module" src="\.\/flight-recorder\.js"/);
});

test("Flight Recorder retains responsive, touch, focus, reduced-motion, and forced-colors behavior", async () => {
  const css = await read("../labs/flight-recorder.css");
  assert.match(css, /min-height:\s*48px/);
  assert.match(css, /touch-action:\s*manipulation/);
  assert.match(css, /:focus-visible/);
  assert.match(css, /@media \(max-width:\s*620px\)/);
  assert.match(css, /@media \(prefers-reduced-motion:\s*reduce\)/);
  assert.match(css, /@media \(forced-colors:\s*active\)/);
  assert.match(css, /aria-current="step"/);
});

test("controller uses text-only DOM and never renders authority-bearing bytes or stronger finality", async () => {
  const controller = await read("../labs/flight-recorder-controller.js");
  assert.doesNotMatch(controller, /innerHTML|insertAdjacentHTML|document\.write/);
  assert.doesNotMatch(controller, /judgeInputDigest|judgeOutputDigest/);
  assert.match(controller, /Canon, configuration, and judge input\/output bytes never enter this surface/);
  assert.match(controller, /not itself a quorum-finality certificate/);
  assert.match(controller, /ArrowLeft/);
  assert.doesNotMatch(controller, /Math\.random|crypto\.getRandomValues/);
});

test("shipping entry has fixed config and demo URLs with no query-selected endpoint", async () => {
  const entry = await read("../labs/flight-recorder.js");
  assert.match(entry, /FLIGHT_RECORDER_CONFIG_URL/);
  assert.match(entry, /FLIGHT_RECORDER_DEMO_URL/);
  assert.match(entry, /loadConfiguredFlightRecorder/);
  assert.doesNotMatch(entry, /URLSearchParams|location\.search|searchParams|endpoint-url|authority-id/);
});

test("checked deployment config explicitly selects demo mode", async () => {
  const config = JSON.parse(await read("../labs/flight-recorder.config.json"));
  assert.deepEqual(config, {
    format: "POA-FLIGHT-RECORDER-CONFIG-1",
    mode: "demo",
    api_base_url: null,
    authority_id: null,
    max_transitions: 64,
  });
});
