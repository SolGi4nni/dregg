import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

const SURFACES = [
  "app.js", "platform-terminal.js", "game-rack.js", "run-summary.js", "today-board.js",
  "station-panel.js", "records-view.js", "galley-status.js",
];

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

test("every surface that draws served bytes renders text, never markup", async () => {
  // The rack, the end screen, the today board and the three organ views draw
  // content that came off the wire — a slot commitment, a refusal message, a
  // game name, a node's own `detail` string, a Lean-authored provenance claim.
  // Every one of them goes in as a text node, so there is no path from a served
  // document into the DOM as HTML.
  for (const file of ["game-rack.js", "run-summary.js", "today-board.js", "station-panel.js", "records-view.js", "galley-status.js"]) {
    const source = await readFile(new URL(`../src/${file}`, import.meta.url), "utf8");
    assert.doesNotMatch(source, /\.innerHTML\b|\.outerHTML\b|insertAdjacentHTML/, `${file} writes markup`);
    assert.match(source, /textContent/, `${file} should build text nodes`);
  }
});
