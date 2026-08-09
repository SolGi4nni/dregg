import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
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

const DEPLOYMENTS = new URL("../../poa/deployments/", import.meta.url);

/**
 * The one checked-in deployment manifest, or a refusal that says what to do.
 *
 * ⚑ THE EPOCH IS DISCOVERED, NOT SPELLED. This used to open
 * `poa/deployments/epoch-1/poa-devnet.json` by a hard-coded path, which made the
 * tripwire fail OPEN at exactly the moment it exists for. `REGENESIS-RUNBOOK-
 * 2026-08-08.md` §10 requires the old root to be RETAINED until the ceremony is
 * signed off — so a re-genesis to epoch-2 leaves `epoch-1/` in place, this test
 * goes on comparing the extension constant against the RETIRED federation, and
 * passes green while every claim the extension signs is refused by the live node.
 * That is the same wound the pin was written to close, one level up.
 *
 * So: enumerate. Zero manifests and two manifests are both refusals with their
 * own message, because during a ceremony the constant genuinely IS ambiguous and
 * the only safe verdict is to make a human say which epoch the extension ships
 * against.
 */
function soleDeployment(root = DEPLOYMENTS) {
  const epochs = readdirSync(root, { withFileTypes: true })
    .filter((entry) => entry.isDirectory())
    .map((entry) => entry.name)
    .filter((name) => {
      try {
        readFileSync(new URL(`${name}/poa-devnet.json`, root));
        return true;
      } catch {
        return false;
      }
    })
    .sort();
  assert.notEqual(
    epochs.length,
    0,
    `no poa/deployments/*/poa-devnet.json exists, so POA_SIGNAL_FEDERATION_HEX is pinned ` +
      `against nothing. Re-genesis moved or removed the deployment kit: point ` +
      `extension/src/poa-signal.ts at the new manifest and update this test's path root.`,
  );
  assert.equal(
    epochs.length,
    1,
    `poa/deployments/ holds ${epochs.length} deployment manifests (${epochs.join(", ")}), so ` +
      `"the checked-in federation" no longer names one value. A re-genesis is in flight and ` +
      `the runbook retains the old root until sign-off — decide which epoch the extension ` +
      `ships against, re-point POA_SIGNAL_FEDERATION_HEX in extension/src/poa-signal.ts, and ` +
      `delete the retired root. Do NOT relax this check to "the newest one": that is how the ` +
      `extension came to sign 4ea83e8e… claims against a 70b7fa4c… node.`,
  );
  const path = `${epochs[0]}/poa-devnet.json`;
  const manifest = JSON.parse(readFileSync(new URL(path, root), "utf8"));
  assert.match(
    manifest.federation_id ?? "",
    /^[0-9a-f]{64}$/,
    `poa/deployments/${path} has no 64-hex federation_id, so this pin would compare the ` +
      `extension constant against undefined and any value would look wrong for the wrong ` +
      `reason. The deployment manifest schema changed; fix the reader, not the constant.`,
  );
  return manifest;
}

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
  const deployment = soleDeployment();
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

test("the deployment pin actually refuses a retained-old-root re-genesis", () => {
  // ⚠ THE REAL READER OVER THE REAL SHAPE, in a scratch tree, because the failure
  // this guards is a state the repo is not in yet and a check nobody has watched
  // go red is a check nobody has. Each case is asserted to have been CONSTRUCTED
  // before its verdict is read, so the falsifier cannot quietly become a no-op.
  const root = mkdtempSync(join(tmpdir(), "poa-deployments-")) + "/";
  const rootUrl = pathToFileURL(root);
  const write = (epoch, body) => {
    mkdirSync(join(root, epoch), { recursive: true });
    writeFileSync(join(root, epoch, "poa-devnet.json"), JSON.stringify(body));
  };
  const live = { federation_id: "70b7fa4c".padEnd(64, "0") };

  // Zero.
  assert.deepEqual(readdirSync(root), [], "the empty case must actually be empty");
  assert.throws(() => soleDeployment(rootUrl), /pinned against nothing/);

  // One — the state the repo is in, and the only one that may pass.
  write("epoch-1", live);
  assert.equal(soleDeployment(rootUrl).federation_id, live.federation_id);

  // Two: the ceremony retains the old root. This is the fail-open that was here.
  write("epoch-2", { federation_id: "aa".repeat(32) });
  assert.equal(readdirSync(root).length, 2, "the retained-root mutation must actually add a root");
  assert.throws(() => soleDeployment(rootUrl), /holds 2 deployment manifests \(epoch-1, epoch-2\)/);

  // A manifest whose schema moved must not be compared against `undefined`.
  rmSync(join(root, "epoch-2"), { recursive: true });
  write("epoch-1", { federation: live.federation_id });
  assert.throws(() => soleDeployment(rootUrl), /no 64-hex federation_id/);

  rmSync(root, { recursive: true });
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
