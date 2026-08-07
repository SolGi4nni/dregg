import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  POA_SIGNAL_BETA_ORIGIN,
  POA_SIGNAL_FEDERATION_HEX,
  POA_SIGNAL_MISSION_ID,
  POA_SIGNAL_NODE_URL,
  POA_SIGNAL_MAX_ROUNDS,
  POA_SIGNAL_SCHEMA,
  explainPoASignalClaim,
  parsePoASignalClaim,
} from "./.build/poa-signal.mjs";

// ⚑ A THREE-ROUND RUN. The claim carries the transcript that was played, not the
// solving code, so a one-round fixture would exercise the only shape that used
// to exist and none of what changed.
const good = () => ({
  schema: POA_SIGNAL_SCHEMA,
  missionId: POA_SIGNAL_MISSION_ID,
  transcript: [[0, 0, 0], [3, 3, 3], [2, 4, 1]],
});

test("PoA Signal deployment pins are exact and contain no Basic Auth credential", () => {
  assert.equal(POA_SIGNAL_BETA_ORIGIN, "https://beta.pathofangels.network");
  assert.equal(POA_SIGNAL_NODE_URL, "https://node.pathofangels.network");

  // ⚠ NOT a literal. This assertion used to compare the constant against a
  // hand-copied spelling of itself — a pin against its own definition, which
  // stayed green for as long as both copies were wrong together, and they were:
  // the deployment moved to 70b7fa4c… and the extension went on signing claims
  // under 4ea83e8e…, a federation the live node answers 400 for. Two
  // INDEPENDENT sources that must agree is a gate; one source quoted twice is
  // decoration.
  const deployment = JSON.parse(
    readFileSync(
      new URL("../../poa/deployments/epoch-1/poa-devnet.json", import.meta.url),
      "utf8",
    ),
  );
  assert.equal(
    POA_SIGNAL_FEDERATION_HEX,
    deployment.federation_id,
    "the extension signs Signal claims under a different federation than the checked-in " +
      "deployment; every claim it posts would be refused by the node's authority selector",
  );
  assert.equal(POA_SIGNAL_FEDERATION_HEX.length, 64);
  const exported = JSON.stringify({
    POA_SIGNAL_BETA_ORIGIN,
    POA_SIGNAL_NODE_URL,
    POA_SIGNAL_FEDERATION_HEX,
  });
  assert.doesNotMatch(exported, /eden|basic|authorization/i);
});

test("claim accepts and copies only schema + mission 1 + a played transcript", () => {
  const input = good();
  const parsed = parsePoASignalClaim(input);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.claim, good());

  // Substitution-proof, PER ROUND. A shallow copy of an array of arrays would
  // leave every round aliased to the page's object, so mutating a band after
  // consent was painted would change the claim that gets built — which is the
  // exact substitution this copy exists to prevent, one nesting level down.
  input.transcript[2][0] = 5;
  input.transcript[0] = [1, 1, 1];
  assert.deepEqual(
    parsed.claim.transcript,
    [[0, 0, 0], [3, 3, 3], [2, 4, 1]],
    "validated claim is a substitution-proof DEEP copy",
  );
});

test("the old one-code claim shape is REFUSED, not reinterpreted", () => {
  // ⚑ THE FLAG DAY, from the page's side. A claim naming `code` was the whole
  // blind path: the node now refuses a claim whose rounds it never classified,
  // so a page still posting one code must be told here rather than have a turn
  // rejected on chain after a consent dialog it already agreed to.
  const legacy = { schema: POA_SIGNAL_SCHEMA, missionId: POA_SIGNAL_MISSION_ID, code: [2, 4, 1] };
  const parsed = parsePoASignalClaim(legacy);
  assert.equal(parsed.ok, false);
  assert.match(parsed.error, /exactly schema, missionId, and transcript/);

  // …and it is not accepted by carrying BOTH, either.
  assert.equal(parsePoASignalClaim({ ...good(), code: [2, 4, 1] }).ok, false);
});

test("authority and effect injection are refused even when the public claim is valid", () => {
  for (const [key, value] of [
    ["federationId", "ff".repeat(32)],
    ["nodeUrl", "https://evil.invalid"],
    ["signer", "aa".repeat(32)],
    ["nonce", 9],
    ["previousReceiptHash", "bb".repeat(32)],
    ["reward", 1000],
    ["effects", [{ Transfer: { amount: 1000 } }]],
    ["memo", "smuggled"],
  ]) {
    const injected = { ...good(), [key]: value };
    const parsed = parsePoASignalClaim(injected);
    assert.equal(parsed.ok, false, `${key} injection refused`);
    assert.match(parsed.error, /exactly schema, missionId, and transcript/);
  }
});

test("wrong schema, mission, run length, arity and out-of-range bands refuse", () => {
  const over = Array.from({ length: POA_SIGNAL_MAX_ROUNDS + 1 }, () => [0, 0, 0]);
  const cases = [
    { ...good(), schema: "poa-signal-claim/v2" },
    { ...good(), missionId: 2 },
    // A run with no rounds is not a game, and a sixth burst is one the judge's
    // `replay` refuses at the step — after the player already paid a turn fee.
    { ...good(), transcript: [] },
    { ...good(), transcript: over },
    { ...good(), transcript: [[1, 2]] },
    { ...good(), transcript: [[1, 2, 3, 4]] },
    { ...good(), transcript: [[-1, 2, 3]] },
    { ...good(), transcript: [[6, 2, 3]] },
    { ...good(), transcript: [[1.5, 2, 3]] },
    { ...good(), transcript: [["1", 2, 3]] },
    // A bad round in a LATER position must refuse too: a loop that validated
    // only the first round would pass this and hand the builder an illegal band.
    { ...good(), transcript: [[0, 0, 0], [3, 3, 3], [6, 4, 1]] },
    { ...good(), transcript: [[0, 0, 0], "not-a-round", [2, 4, 1]] },
  ];
  for (const input of cases) {
    assert.equal(parsePoASignalClaim(input).ok, false, JSON.stringify(input.transcript));
  }
  assert.equal(
    parsePoASignalClaim({ ...good(), transcript: over.slice(1) }).ok,
    true,
    `exactly ${POA_SIGNAL_MAX_ROUNDS} rounds is the budget, not one past it`,
  );
});

test("consent is exact, transparent, non-economic, and admission-honest", () => {
  const text = explainPoASignalClaim({
    missionId: 1,
    transcript: [[0, 0, 0], [3, 3, 3], [2, 4, 1]],
    signerPublicKeyHex: "11".repeat(32),
    agentCellId: "22".repeat(32),
    nonce: 7,
    previousReceiptHashHex: "33".repeat(32),
    federationHex: POA_SIGNAL_FEDERATION_HEX,
    fee: 210,
    turnHash: "44".repeat(32),
  });
  assert.match(text, /Mission: 1/);
  // ⚠ THE CONSENT NAMES EVERY BURST. A reader agreeing to "publish my code"
  // while the turn carries three is being told the wrong thing about what leaves
  // their machine, so the dialog shows the run and the count, and this asserts it
  // on the rendered text rather than trusting the template.
  assert.match(text, /Signal transcript \(3 of 5 bursts\): 0 · 0 · 0  →  3 · 3 · 3  →  2 · 4 · 1/);
  assert.match(text, /Solving code: 2 · 4 · 1/);
  assert.match(text, /transfers no DREGG, mints no reward, and grants no capability/);
  assert.match(text, new RegExp(POA_SIGNAL_FEDERATION_HEX));
  assert.match(text, /Turn nonce: 7/);
  assert.match(text, new RegExp(`Previous receipt: ${"33".repeat(32)}`));
  assert.match(text, /may admit this turn before consensus records/);
  assert.match(text, new RegExp(`\\[turn ${"44".repeat(32)}\\]`));
});
