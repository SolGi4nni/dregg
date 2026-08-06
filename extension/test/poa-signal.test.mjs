import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  POA_SIGNAL_BETA_ORIGIN,
  POA_SIGNAL_FEDERATION_HEX,
  POA_SIGNAL_MISSION_ID,
  POA_SIGNAL_NODE_URL,
  POA_SIGNAL_SCHEMA,
  explainPoASignalClaim,
  parsePoASignalClaim,
} from "./.build/poa-signal.mjs";

const good = () => ({
  schema: POA_SIGNAL_SCHEMA,
  missionId: POA_SIGNAL_MISSION_ID,
  code: [2, 4, 1],
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

test("claim accepts and copies only schema + mission 1 + three base-six bands", () => {
  const input = good();
  const parsed = parsePoASignalClaim(input);
  assert.equal(parsed.ok, true);
  assert.deepEqual(parsed.claim, good());
  input.code[0] = 5;
  assert.deepEqual(parsed.claim.code, [2, 4, 1], "validated claim is substitution-proof copy");
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
    assert.match(parsed.error, /exactly schema, missionId, and code/);
  }
});

test("wrong schema, mission, arity and out-of-range/non-integer bands refuse", () => {
  const cases = [
    { ...good(), schema: "poa-signal-claim/v2" },
    { ...good(), missionId: 2 },
    { ...good(), code: [1, 2] },
    { ...good(), code: [1, 2, 3, 4] },
    { ...good(), code: [-1, 2, 3] },
    { ...good(), code: [6, 2, 3] },
    { ...good(), code: [1.5, 2, 3] },
    { ...good(), code: ["1", 2, 3] },
  ];
  for (const input of cases) assert.equal(parsePoASignalClaim(input).ok, false);
});

test("consent is exact, transparent, non-economic, and admission-honest", () => {
  const text = explainPoASignalClaim({
    missionId: 1,
    code: [2, 4, 1],
    signerPublicKeyHex: "11".repeat(32),
    agentCellId: "22".repeat(32),
    nonce: 7,
    previousReceiptHashHex: "33".repeat(32),
    federationHex: POA_SIGNAL_FEDERATION_HEX,
    fee: 210,
    turnHash: "44".repeat(32),
  });
  assert.match(text, /Mission: 1/);
  assert.match(text, /Signal code: 2 · 4 · 1/);
  assert.match(text, /transfers no DREGG, mints no reward, and grants no capability/);
  assert.match(text, new RegExp(POA_SIGNAL_FEDERATION_HEX));
  assert.match(text, /Turn nonce: 7/);
  assert.match(text, new RegExp(`Previous receipt: ${"33".repeat(32)}`));
  assert.match(text, /may admit this turn before consensus records/);
  assert.match(text, new RegExp(`\\[turn ${"44".repeat(32)}\\]`));
});
