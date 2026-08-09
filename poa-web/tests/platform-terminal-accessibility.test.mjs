import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const read = (path) => readFile(new URL(path, import.meta.url), "utf8");

test("the primary terminal exposes all seven platform routes and exact lab entries", async () => {
  const html = await read("../index.html");
  for (const route of ["overview", "missions", "galley", "crew", "records", "bazaar", "choir"]) {
    assert.match(html, new RegExp(`data-route="${route}"`));
    assert.match(html, new RegExp(`data-view="${route}"`));
  }
  for (const lab of ["expedition-lab.html", "archive-lab.html", "flight-recorder.html"]) {
    assert.match(html, new RegExp(`href="\\./labs/${lab}"`));
  }
  for (const id of ["platform-terminal", "crew-systems", "evidence-register", "bazaar-gates"]) {
    assert.match(html, new RegExp(`id="${id}"[^>]*aria-live="polite"`));
  }
  // Five separate green lights, and the page must say none of them upgrades
  // another — laundering one into the rest is the whole failure this guards.
  // The count went four → five when the JUDGED run stopped being folded into
  // the practice run's caveat; those two are the ones most easily laundered
  // into each other, so the copy names them apart explicitly.
  assert.match(html, /Five different green lights/);
  assert.match(html, /None of them upgrades another/);
  assert.match(html, /the last two are not the same light/);
  assert.match(html, /no profile, no owned kit, no progression, no injury record/i);
});

test("platform rendering uses text nodes and links without inline styles or click-only cards", async () => {
  const source = await read("../src/platform-terminal.js");
  assert.doesNotMatch(source, /\.innerHTML\b|\.outerHTML\b|\.style\b|setAttribute\(["']style/);
  assert.match(source, /element\("a", "platform-card__link"/);
  assert.match(source, /row\.setAttribute\("aria-disabled", "true"\)/);
  assert.match(source, /No control here settles, signs, or promotes/);
});

test("platform navigation remains keyboard-visible and fits seven routes on mobile", async () => {
  const css = await read("../styles.css");
  assert.match(css, /\.rail nav \{[^}]*grid-template-columns:\s*repeat\(7,\s*1fr\)/s);
  assert.match(css, /\.platform-card__link:focus-visible/);
  assert.match(css, /\.primary-link:focus-visible/);
  assert.match(css, /prefers-reduced-motion:\s*reduce/);
  assert.match(css, /\.rail nav a \{[^}]*min-height:\s*46px/s);
});
