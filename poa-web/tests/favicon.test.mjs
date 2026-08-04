import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

test("the terminal declares a local repo-native SVG favicon", async () => {
  const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
  const icon = await readFile(new URL("../favicon.svg", import.meta.url), "utf8");
  assert.match(html, /<link rel="icon" href="\.\/favicon\.svg" type="image\/svg\+xml" \/>/);
  assert.match(icon, /^<svg xmlns=/);
  assert.doesNotMatch(icon, /(?:href|src)=["'](?:data:|https?:\/\/)/);
});
