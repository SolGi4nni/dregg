import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("the primary terminal exposes all six platform routes and exact lab entries", async () => {
  const html = await read("../index.html");
  for (const route of ["overview", "missions", "crew", "records", "bazaar", "choir"]) {
    assert.match(html, new RegExp(`data-route="${route}"`));
    assert.match(html, new RegExp(`data-view="${route}"`));
  }
  for (const lab of ["expedition-lab.html", "archive-lab.html", "flight-recorder.html"]) {
    assert.match(html, new RegExp(`href="\\./labs/${lab}"`));
  }
  for (const id of ["platform-terminal", "crew-systems", "evidence-register", "bazaar-gates"]) {
    assert.match(html, new RegExp(`id="${id}"[^>]*aria-live="polite"`));
  }
  assert.match(html, /Content authentication, table provenance, replay continuity, and settlement are separate claims/);
  assert.match(html, /no persistent officer profile, crew custody object, progression receipt, or injury ledger/i);
});

test("platform rendering uses text nodes and links without inline styles or click-only cards", async () => {
  const source = await read("../src/platform-terminal.js");
  assert.doesNotMatch(source, /\.innerHTML\b|\.outerHTML\b|\.style\b|setAttribute\(["']style/);
  assert.match(source, /element\("a", "platform-card__link"/);
  assert.match(source, /row\.setAttribute\("aria-disabled", "true"\)/);
  assert.match(source, /No control here settles, signs, or promotes/);
});

test("platform navigation remains keyboard-visible and fits six routes on mobile", async () => {
  const css = await read("../styles.css");
  assert.match(css, /\.rail nav \{[^}]*grid-template-columns:\s*repeat\(6,\s*1fr\)/s);
  assert.match(css, /\.platform-card__link:focus-visible/);
  assert.match(css, /\.primary-link:focus-visible/);
  assert.match(css, /prefers-reduced-motion:\s*reduce/);
  assert.match(css, /\.rail nav a \{[^}]*min-height:\s*46px/s);
});
