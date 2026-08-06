import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const SURFACES = ["app.js", "platform-terminal.js", "game-rack.js", "run-summary.js", "today-board.js"];

test("the PoA surface works under infra's style-src self policy", async () => {
  const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
  const server = await readFile(new URL("../serve.mjs", import.meta.url), "utf8");
  assert.doesNotMatch(html, /\sstyle\s*=/i);
  for (const file of SURFACES) {
    const source = await readFile(new URL(`../src/${file}`, import.meta.url), "utf8");
    assert.doesNotMatch(source, /\.style\b|setAttribute\(["']style/, `${file} styles inline`);
  }
  assert.match(server, /style-src 'self'/);
  assert.doesNotMatch(server, /style-src[^;"]*unsafe-inline/);
});

test("the rack, the end screen, and the today board render text, never markup", async () => {
  // The rack and the end screen draw content that came off the wire — a slot
  // commitment, a refusal message, a game name. Every one of them goes in as a
  // text node, so there is no path from a served document into the DOM as HTML.
  for (const file of ["game-rack.js", "run-summary.js", "today-board.js"]) {
    const source = await readFile(new URL(`../src/${file}`, import.meta.url), "utf8");
    assert.doesNotMatch(source, /\.innerHTML\b|\.outerHTML\b|insertAdjacentHTML/, `${file} writes markup`);
    assert.match(source, /textContent/, `${file} should build text nodes`);
  }
});
