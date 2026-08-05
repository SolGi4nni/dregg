import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

test("the PoA surface works under infra's style-src self policy", async () => {
  const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
  const app = await readFile(new URL("../src/app.js", import.meta.url), "utf8");
  const platform = await readFile(new URL("../src/platform-terminal.js", import.meta.url), "utf8");
  const server = await readFile(new URL("../serve.mjs", import.meta.url), "utf8");
  assert.doesNotMatch(html, /\sstyle\s*=/i);
  assert.doesNotMatch(app, /\.style\b|setAttribute\(["']style/);
  assert.doesNotMatch(platform, /\.style\b|setAttribute\(["']style/);
  assert.match(server, /style-src 'self'/);
  assert.doesNotMatch(server, /style-src[^;"]*unsafe-inline/);
});
