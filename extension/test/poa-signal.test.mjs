import { test } from "node:test";
import assert from "node:assert/strict";
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
  assert.equal(
    POA_SIGNAL_FEDERATION_HEX,
    "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a",
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
