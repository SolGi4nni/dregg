import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { test } from "node:test";

test("main mission surface mounts restrained optional admission below the games", async () => {
  const html = await readFile(new URL("../index.html", import.meta.url), "utf8");
  const app = await readFile(new URL("../src/app.js", import.meta.url), "utf8");
  assert.match(html, /dregg-admission-panel\.css/u);
  assert.match(html, /mission-layout[\s\S]*dregg-admission-root[\s\S]*<\/section>/u);
  // The claim, not the wording: no wallet or no node means NOTHING IS ADMITTED.
  assert.match(html, /If no wallet answers, or the node on this origin does not, nothing is admitted/u);
  assert.match(app, /mountDreggAdmissionPanel/u);
  assert.match(app, /getWalletStandardRegistry\(window\)/u);
  assert.match(app, /PoA wallet admission unavailable/u);
  assert.doesNotMatch(app, /onAdmissionChange|setHoldingCredential\(credential\)/u,
    "local RPC holding receipts are not federation-verifiable Galley eligibility");
  assert.match(app, /createGalleyTransport/u);
  assert.match(app, /mountGalley/u);
  assert.doesNotMatch(app, /credential\.(?:score|progress|vote|balance)/u,
    "the local receipt cannot become browser game authority");
  assert.doesNotMatch(html, /governance (?:enabled|active)|verified balance/iu);
});
