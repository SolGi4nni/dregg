import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("primary terminal exposes Galley as a seventh keyboard route with an honest signer boundary", async () => {
  const html = await read("../index.html");
  assert.match(html, /data-route="galley"/);
  assert.match(html, /data-view="galley"/);
  assert.match(html, /id="galley-root"/);
  assert.match(html, /live journal needs permission to share an active Dregg public key/);
  assert.match(html, /exact turn postcard to the actual Dregg signer/);

  const css = await read("../styles.css");
  assert.match(css, /\.rail nav \{[^}]*grid-template-columns:\s*repeat\(7,\s*1fr\)/s);
  assert.match(css, /\.galley-action:hover:not\(:disabled\),\s*\.galley-action:focus-visible/);
  assert.match(css, /\.galley-projection:focus-visible/);
  assert.match(css, /@media \(prefers-reduced-motion:\s*reduce\)/);
});

test("controller uses native controls, a labeled live region, and safe text-only rendering", async () => {
  const source = await read("../src/galley-controller.js");
  assert.match(source, /live\.setAttribute\("role", "status"\)/);
  assert.match(source, /live\.setAttribute\("aria-live", "polite"\)/);
  assert.match(source, /control\.setAttribute\("aria-describedby", live\.id\)/);
  assert.match(source, /control\.addEventListener\("keydown"/);
  assert.match(source, /documentRef, "button"/);
  assert.match(source, /JSON\.stringify\(publicPlayProjection, null, 2\)/);
  assert.doesNotMatch(source, /\.innerHTML\b|\.outerHTML\b|\.style\b|setAttribute\(["']style/);
  assert.doesNotMatch(source, /pay.?to.?win/i);
});

test("browser has no parallel wire, caller-authored player, reducer, or persisted game-state twin", async () => {
  const runtime = await read("../src/galley-runtime.js");
  const controller = await read("../src/galley-controller.js");
  const source = `${runtime}\n${controller}`;
  for (const format of [
    "POA-GALLEY-SESSION-V1",
    "POA-GALLEY-STATUS-V1",
    "POA-GALLEY-COMMAND-PREPARE-V1",
    "POA-GALLEY-UNSIGNED-TURN-V1",
    "POA-GALLEY-PENDING-INTENT-JOURNAL-V2",
  ]) assert.match(runtime, new RegExp(format, "u"));
  assert.doesNotMatch(source, /poa-galley-node-view-v1|poa-galley-session-request-v1|expected_head_digest/);
  assert.doesNotMatch(runtime, /player_public_key|playerPublicKey|holding_receipt_id/);
  assert.match(runtime, /Durable local journal of intent coordinates only; never a Galley state twin/);
  assert.doesNotMatch(source, /sessionStorage|indexedDB/);
  assert.doesNotMatch(runtime, /expires_at/);
  assert.doesNotMatch(controller, /postcard verified|verified postcard/i);
  assert.doesNotMatch(source, /score\s*[+\-*/]?=/i);
  assert.doesNotMatch(source, /progress\s*\+=|revision\s*\+=|sequence\s*\+=/);
  assert.doesNotMatch(source, /function\s+(?:reduce|transition|score|judge)\b/i);
  assert.match(runtime, /const PROJECTION_KEYS = Object\.freeze/);
  assert.match(runtime, /const EVENT_PAYLOAD_KEYS = Object\.freeze/);
  assert.match(runtime, /projectGalleyWatch/);
  assert.match(controller, /publicPlayProjection/);
  assert.match(controller, /documentRef, "details"/);
  assert.match(controller, /documentRef, "summary"/);
  assert.doesNotMatch(source, /holder_sponsorship|holder sponsorship/i);
});
