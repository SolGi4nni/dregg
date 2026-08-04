import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("standalone archive has skip, live provenance state, fixed source, and explicit beta boundary", async () => {
  const html = await read("../labs/archive-lab.html");
  assert.match(html, /class="archive-skip" href="#archive-lab"/);
  assert.match(html, /id="archive-lab" tabindex="-1" aria-busy="true"/);
  assert.match(html, /id="descriptor-status"[^>]*role="status"[^>]*aria-live="polite"/);
  assert.match(html, /BUILT-IN SOURCE ONLY/);
  assert.match(html, /Custom and query-selected descriptors are disabled/);
  assert.match(html, /BETA-ONLY DEMONSTRATOR/);
  assert.doesNotMatch(html, /<form|<input|name="descriptor"|name="sha256"/);
  assert.match(html, /type="module" src="\.\/archive-lab\.js"/);
});

test("archive CSS retains touch, keyboard, reduced-motion, mobile, and forced-colors affordances", async () => {
  const css = await read("../labs/archive-lab.css");
  assert.match(css, /min-height:\s*48px/);
  assert.match(css, /touch-action:\s*manipulation/);
  assert.match(css, /:focus-visible/);
  assert.match(css, /@media \(max-width:\s*560px\)/);
  assert.match(css, /@media \(prefers-reduced-motion:\s*reduce\)/);
  assert.match(css, /@media \(forced-colors:\s*active\)/);
  assert.match(css, /aria-current="location"/);
});

test("archive controller is text-only, keeps refusals operable, and states the authority boundary", async () => {
  const controller = await read("../labs/archive-lab-controller.js");
  assert.doesNotMatch(controller, /innerHTML|insertAdjacentHTML|document\.write/);
  assert.match(controller, /aria-live/);
  assert.doesNotMatch(controller, /aria-disabled/);
  assert.match(controller, /ArrowLeft/);
  assert.match(controller, /do not promote canon, mint an asset, settle a reward/);
  assert.doesNotMatch(controller, /Math\.random|crypto\.getRandomValues/);
});

test("shipping archive entry ignores query overrides and accepts only the built-in provenance loader", async () => {
  const entry = await read("../labs/archive-lab.js");
  assert.match(entry, /fetchBuiltinArchiveLabDescriptor/);
  assert.match(entry, /PINNED_ARCHIVE_PROVENANCE_URL/);
  assert.doesNotMatch(entry, /URLSearchParams|location\.search|searchParams|descriptor-url|descriptor-sha/);
});
