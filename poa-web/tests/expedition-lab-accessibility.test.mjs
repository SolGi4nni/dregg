import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("the standalone lab has a skip target, live provenance state, no custom source controls, and an explicit boundary", async () => {
  const html = await read("../labs/expedition-lab.html");
  assert.match(html, /class="expedition-skip" href="#expedition-lab"/);
  assert.match(html, /id="expedition-lab" tabindex="-1" aria-busy="true"/);
  assert.match(html, /id="descriptor-status"[^>]*role="status"[^>]*aria-live="polite"/);
  assert.match(html, /BUILT-IN SOURCE ONLY/);
  assert.match(html, /Custom and query-selected descriptors are disabled/);
  assert.doesNotMatch(html, /<form|<input|name="descriptor"|name="sha256"/);
  assert.match(html, /NON-CANON DEMONSTRATOR/);
  assert.match(html, /type="module" src="\.\/expedition-lab\.js"/);
});

test("the lab keeps touch, keyboard, reduced-motion, mobile, and forced-colors affordances", async () => {
  const css = await read("../labs/expedition-lab.css");
  assert.match(css, /min-height:\s*48px/);
  assert.match(css, /touch-action:\s*manipulation/);
  assert.match(css, /:focus-visible/);
  assert.match(css, /@media \(max-width:\s*560px\)/);
  assert.match(css, /@media \(prefers-reduced-motion:\s*reduce\)/);
  assert.match(css, /@media \(forced-colors:\s*active\)/);
  assert.match(css, /aria-current="location"/);
});

test("the controller builds text-only DOM and does not smuggle reward or canon claims into the experience", async () => {
  const controller = await read("../labs/expedition-lab-controller.js");
  assert.doesNotMatch(controller, /innerHTML|insertAdjacentHTML|document\.write/);
  assert.match(controller, /aria-live/);
  assert.doesNotMatch(controller, /aria-disabled/);
  assert.match(controller, /ArrowLeft/);
  assert.match(controller, /Candidate observations remain provisional/);
  assert.match(controller, /No result here promotes canon, mints an asset, settles a reward/);
  assert.doesNotMatch(controller, /Math\.random|crypto\.getRandomValues/);
});

test("the shipping entry point ignores query overrides and uses only the built-in provenance loader", async () => {
  const entry = await read("../labs/expedition-lab.js");
  assert.match(entry, /fetchBuiltinExpeditionDescriptor/);
  assert.match(entry, /PINNED_PROVENANCE_URL/);
  assert.doesNotMatch(entry, /URLSearchParams|location\.search|searchParams|descriptor-url|descriptor-sha/);
});
