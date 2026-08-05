import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

test("main mission surface mounts restrained optional admission below the games", async () => {
  const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
  const app = await readFile(new URL("../src/app.js", import.meta.url), "utf8");
  assert.match(html, /dregg-admission-panel\.css/u);
  assert.match(html, /mission-layout[\s\S]*dregg-admission-root[\s\S]*<\/section>/u);
  assert.match(html, /If Wallet Standard discovery or the same-origin PoA node is unavailable, no access will be granted/u);
  assert.match(app, /mountDreggAdmissionPanel/u);
  assert.match(app, /getWalletStandardRegistry\(window\)/u);
  assert.match(app, /PoA wallet admission unavailable/u);
  assert.doesNotMatch(app, /onAdmissionChange/u, "client receipt must not become local game authority");
  assert.doesNotMatch(html, /governance (?:enabled|active)|verified balance/iu);
});
