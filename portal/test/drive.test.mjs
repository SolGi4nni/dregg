// The portal drive layer, round-tripped against a local node.
//
// This drives the EXACT functions the interactive portal fires
// (`src/drive-actions.mjs`) through a mock node that verifies each submitted
// envelope the way the real node ingress (`post_submit_signed_turn`) does:
// the postcard frame `turn ++ 0x40 ++ sig(64) ++ 0x20 ++ signer(32)`, the
// signer == the submitting identity, and the turn's agent ==
// `derive_raw(signer, blake3("default"))`. For the per-action credential it
// re-verifies the Ed25519 signature over the canonical federation-bound
// `actionSigningMessage` using `@dregg/sdk/raw` — the same check the executor
// makes. So a turn that this test accepts is a turn the node accepts.
//
// Everything here imports the PUBLISHED @dregg/sdk from node_modules (the
// portal is a real consumer), exactly as the browser bundle does.

import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";

import { Identity, AgentRuntime, symbol } from "@dregg/sdk";
import {
  deriveCellId,
  blake3,
  actionSigningMessage,
  ed25519Verify,
  concatBytes,
} from "@dregg/sdk/raw";

import {
  fireTransfer,
  publishMinisite,
  openLease,
  fundLease,
  siteContentHash,
  SITE_CONTENT_SLOT,
  hexToBytes,
} from "../src/drive-actions.mjs";

const hex = (b) => Buffer.from(b).toString("hex");

/** A mock node that verifies every submitted envelope like the real ingress
 * and serves the read routes the SDK runtime needs (identity, federations,
 * cell, receipts). Records each verified envelope for assertions. */
async function mockNode() {
  const nodePubkey = Uint8Array.from({ length: 32 }, () => 5);
  const seen = [];
  const receipts = [];
  let counter = 0;

  const server = createServer((req, res) => {
    const send = (code, body) => {
      res.writeHead(code, { "content-type": "application/json" });
      res.end(JSON.stringify(body));
    };
    if (req.url === "/api/node/identity") {
      return send(200, {
        public_key: hex(nodePubkey),
        agent_cell: "00".repeat(32),
        unlocked: true,
        agent_balance: 0,
        agent_nonce: 0,
      });
    }
    if (req.url === "/api/federations") {
      // Unconfigured solo node: the executor binds blake3(operator pubkey).
      return send(200, [
        { id: "00".repeat(32), federation_id: "00".repeat(32), committee_epoch: 0, member_count: 0, is_local: true },
      ]);
    }
    if (req.url?.startsWith("/api/cell/")) {
      return send(200, { id: req.url.slice("/api/cell/".length), found: true, balance: 1000, nonce: 0, public_key: "", fields: [] });
    }
    if (req.url === "/api/receipts") {
      return send(200, receipts);
    }
    if (req.url === "/api/turns/submit-signed" && req.method === "POST") {
      const chunks = [];
      req.on("data", (c) => chunks.push(c));
      req.on("end", () => {
        const body = new Uint8Array(Buffer.concat(chunks));
        // Verify the envelope EXACTLY like post_submit_signed_turn.
        const turnBytes = body.subarray(0, body.length - (1 + 64 + 1 + 32));
        assert.equal(body[turnBytes.length], 0x40, "envelope: sig length tag");
        assert.equal(body[turnBytes.length + 65], 0x20, "envelope: signer length tag");
        const signer = body.subarray(turnBytes.length + 66);
        const expectedAgent = deriveCellId(signer);
        // The turn bytes BEGIN with the agent cell id (postcard field order),
        // which must equal derive_raw(signer, blake3("default")).
        assert.equal(hex(turnBytes.subarray(0, 32)), hex(expectedAgent), "turn.agent == derive_raw(signer)");
        seen.push({ signer: hex(signer), turnBytes });
        const turnHashHex = (counter++).toString(16).padStart(2, "0").repeat(32).slice(0, 64);
        receipts.length = 0; // single-head chain for the test
        receipts.push({
          chain_index: counter, chain_head: true,
          receipt_hash: "ef".repeat(32), turn_hash: turnHashHex,
          agent: hex(expectedAgent), pre_state: "11".repeat(32), post_state: "22".repeat(32),
          timestamp: 1765432100, computrons_used: 100, action_count: 1,
          previous_receipt_hash: null, finality: "tentative",
          was_encrypted: false, was_burn: false, has_proof: false,
        });
        send(200, { accepted: true, turn_hash: turnHashHex, action_count: 1 });
      });
      return;
    }
    send(404, { error: "nope" });
  });
  await new Promise((r) => server.listen(0, r));
  return { server, nodePubkey, seen, url: `http://127.0.0.1:${server.address().port}` };
}

function newRuntime(url, seed = 0x20) {
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => seed + i));
  return { identity, runtime: new AgentRuntime(identity, url) };
}

/** Re-verify a signed action's per-action credential the way the executor does:
 * Ed25519 over actionSigningMessage with federation id = blake3(nodePubkey). */
function assertActionCredential(action, nodePubkey, publicKey) {
  assert.equal(action.authorization.kind, "signature", "action carries a real Ed25519 signature");
  const fedId = blake3(nodePubkey);
  const msg = actionSigningMessage(action, fedId);
  const sig64 = concatBytes(action.authorization.r, action.authorization.s);
  assert.ok(ed25519Verify(publicKey, msg, sig64), "per-action signature verifies over the federation-bound message");
}

test("(c) fire a transfer — real signed turn the node accepts", async () => {
  const node = await mockNode();
  try {
    const { identity, runtime } = newRuntime(node.url, 0x20);
    const to = "99".repeat(32);
    const out = await fireTransfer(runtime, to, 25n);
    assertActionCredential(out.action, node.nodePubkey, identity.publicKey);
    assert.match(out.explain, /transfer 25 computrons/);
    assert.ok(out.receipt.turnHash, "a committed receipt came back");
    assert.equal(node.seen.at(-1).signer, identity.publicKeyHex, "node saw the signer");
    // the effect targets the transfer destination
    assert.equal(hex(out.action.effects[0].to), to);
  } finally {
    node.server.close();
  }
});

test("(a) publish a minisite — content hash committed to slot 0 via a publish turn", async () => {
  const node = await mockNode();
  try {
    const { identity, runtime } = newRuntime(node.url, 0x30);
    const content = "<h1>hello from the portal</h1>";
    const out = await publishMinisite(runtime, "my site", content);
    assertActionCredential(out.action, node.nodePubkey, identity.publicKey);
    // method is the `publish` symbol; one SetField on slot 0 carrying blake3(content).
    assert.equal(hex(out.action.method), hex(symbol("publish")), "method == symbol('publish')");
    const eff = out.action.effects[0];
    assert.equal(eff.kind, "setField");
    assert.equal(eff.index, SITE_CONTENT_SLOT);
    assert.equal(hex(eff.value), hex(siteContentHash(content)), "slot 0 == blake3(content)");
    assert.equal(out.contentHashHex, hex(siteContentHash(content)));
    assert.equal(out.dreggUri, `dregg://${identity.cellIdHex()}`);
    assert.ok(out.receipt.turnHash);
  } finally {
    node.server.close();
  }
});

test("(b) open + run a metered execution lease — gated SetField on slot 4", async () => {
  const node = await mockNode();
  try {
    const { runtime } = newRuntime(node.url, 0x40);
    const out = await openLease(runtime, { maxSteps: 8 });
    assert.equal(out.step, 1, "the durable checkpoint advanced to step 1");
    assert.equal(out.remaining, 7);
    assert.ok(out.receipt.turnHash, "the metered run committed");
    assert.equal(node.seen.length, 1, "exactly one metered turn was submitted");
  } finally {
    node.server.close();
  }
});

test("fund a lease cell — one conserving Transfer into the lease cell", async () => {
  const node = await mockNode();
  try {
    const { identity, runtime } = newRuntime(node.url, 0x50);
    const leaseCell = "77".repeat(32);
    const out = await fundLease(runtime, leaseCell, 100n);
    assert.ok(out.receipt.turnHash, "the funding transfer committed");
    assert.equal(node.seen.at(-1).signer, identity.publicKeyHex);
  } finally {
    node.server.close();
  }
});

test("hexToBytes rejects a malformed cell id", () => {
  assert.throws(() => hexToBytes("nope"), /32-byte/);
  assert.equal(hexToBytes("0x" + "ab".repeat(32)).length, 32);
});
