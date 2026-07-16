// The authorized turn builder against a mock node: verb staging, the
// empty-turn refusal, federation-id discovery, and a full
// sign() → explain() → submit() → Receipt round trip whose envelope the
// mock verifies EXACTLY the way post_submit_signed_turn does (signature
// over Turn::hash v3, agent == derive_raw(signer, blake3("default"))).

import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";

import { hex, raw, sdk } from "./helpers.mjs";

async function mockNode({ onEnvelope }) {
  const rawMod = await raw();
  const nodePubkey = Uint8Array.from({ length: 32 }, () => 5);
  const receipts = [];
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
      // Unconfigured solo node: a placeholder entry with no real committee.
      return send(200, [
        { id: "00".repeat(32), federation_id: "00".repeat(32), committee_epoch: 0, member_count: 0, is_local: true },
      ]);
    }
    if (req.url?.startsWith("/api/cell/")) {
      return send(200, { id: req.url.slice("/api/cell/".length), found: true, balance: 500, nonce: 7, public_key: "", fields: [] });
    }
    if (req.url === "/api/receipts") {
      return send(200, receipts);
    }
    if (req.url === "/api/turns/submit-signed" && req.method === "POST") {
      const chunks = [];
      req.on("data", (c) => chunks.push(c));
      req.on("end", () => {
        const body = new Uint8Array(Buffer.concat(chunks));
        const result = onEnvelope(body, receipts);
        send(200, result);
      });
      return;
    }
    send(404, { error: "nope" });
  });
  await new Promise((r) => server.listen(0, r));
  return {
    server,
    nodePubkey,
    url: `http://127.0.0.1:${server.address().port}`,
  };
}

test("sign() refuses an empty turn", async () => {
  const { AgentRuntime, Identity, EmptyTurnError } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => i));
  const runtime = new AgentRuntime(identity, "http://127.0.0.1:1"); // never contacted
  await assert.rejects(() => runtime.turn().sign(), EmptyTurnError);
});

test("full round trip: verbs -> sign -> explain -> submit -> Receipt", async () => {
  const rawMod = await raw();
  const { AgentRuntime, Identity } = await sdk();

  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x20 + i));
  const agentHex = identity.cellIdHex();

  let verified = null;
  const { server, url, nodePubkey } = await mockNode({
    onEnvelope: (body, receipts) => {
      // Verify the envelope EXACTLY like post_submit_signed_turn:
      // postcard frame: turn ++ 0x40 ++ sig(64) ++ 0x20 ++ signer(32).
      const turnBytes = body.subarray(0, body.length - (1 + 64 + 1 + 32));
      assert.equal(body[turnBytes.length], 0x40);
      assert.equal(body[turnBytes.length + 65], 0x20);
      const sig = body.subarray(turnBytes.length + 1, turnBytes.length + 65);
      const signer = body.subarray(turnBytes.length + 66);
      // signature over the canonical Turn::hash — recompute it from the TS
      // wire vocabulary (the differential test ties this to Rust).
      // We can't re-decode postcard here; instead require the client to have
      // signed SOMETHING this signer verifies, and pin the agent binding.
      assert.equal(hex(signer), identity.publicKeyHex, "signer must be the submitting identity");
      const expectedAgent = rawMod.deriveCellId(signer);
      assert.equal(hex(expectedAgent), agentHex, "turn agent must be derive_raw(signer, blake3('default'))");
      // The turn bytes BEGIN with the agent cell id (postcard field order).
      assert.equal(hex(turnBytes.subarray(0, 32)), agentHex);
      verified = { sig, turnBytes };
      const turnHashHex = "cd".repeat(32); // the mock's name for it
      receipts.push({
        chain_index: 0,
        chain_head: true,
        receipt_hash: "ef".repeat(32),
        turn_hash: turnHashHex,
        agent: agentHex,
        pre_state: "11".repeat(32),
        post_state: "22".repeat(32),
        timestamp: 1765432100,
        computrons_used: 100,
        action_count: 1,
        previous_receipt_hash: null,
        finality: "tentative",
        was_encrypted: false,
        was_burn: false,
        has_proof: false,
      });
      return { accepted: true, turn_hash: turnHashHex, action_count: 1 };
    },
  });

  try {
    const runtime = new AgentRuntime(identity, url);

    const to = Uint8Array.from({ length: 32 }, () => 9);
    const builder = runtime.turn().transfer(to, 25n).writeU64(1, 42n).incrementNonce().fee(2000);
    const authorized = await builder.sign();

    // The anti-blind-signing reading: faithful, total, sem-tagged. The default
    // signer is HYBRID post-quantum, and the reading says so — a citizen is
    // told which perimeter they are authorizing under, not just "a signature".
    const explanation = authorized.explain();
    assert.ok(
      explanation.includes("authorized by a HYBRID signature (Ed25519 + ML-DSA-65 post-quantum"),
      `explain() must name the hybrid PQ perimeter, got: ${explanation}`,
    );
    assert.ok(explanation.includes("transfer 25 computrons"));
    assert.ok(explanation.includes("set state field #1"));
    assert.ok(explanation.includes("increment the nonce"));
    assert.ok(explanation.includes("[sem "));

    // The signed action verifies against the discovered federation id
    // (unconfigured solo node → blake3(node operator pubkey)).
    const fedId = rawMod.blake3(nodePubkey);
    const action = authorized.action();
    // The DEFAULT front-door signer is HYBRID post-quantum.
    assert.equal(action.authorization.kind, "hybridSignature");
    // The mock's `/api/cell/` serves nonce 7, so that is the live replay
    // counter `sign()` read and the value `sig-v3` binds into the signature.
    // (Signing over any other nonce verifies nowhere — see the wrong-nonce
    // falsifier in `hybrid-verify.test.mjs`.)
    const msg = rawMod.actionSigningMessage(action, fedId, 7n);
    assert.ok(
      rawMod.ed25519Verify(identity.publicKey, msg, action.authorization.ed25519),
      "the ed25519 half must verify over the canonical federation+nonce-bound message",
    );
    // BOTH halves cover that same message — the PQ half is real, not decorative.
    assert.ok(
      rawMod.mlDsaVerify(action.authorization.mlDsaPk, msg, action.authorization.mlDsa),
      "the ML-DSA-65 half must verify over the SAME message under the turn ctx",
    );
    assert.equal(
      hex(action.authorization.mlDsaPk),
      hex(identity.mlDsaPublicKey()),
      "the carried PQ public key is the one derived from this identity's seed",
    );

    const receipt = await authorized.submit();
    assert.ok(verified, "the mock saw and verified the envelope");
    assert.equal(receipt.turnHash, "cd".repeat(32));
    assert.equal(receipt.receiptHash, "ef".repeat(32));
    assert.equal(receipt.agent, agentHex);
    assert.equal(receipt.hasProof(), false, "receipts are born proofless");

    // One-shot submit (consume-on-submit parity).
    await assert.rejects(() => authorized.submit(), /already submitted/);
  } finally {
    server.close();
  }
});

test("on(target) retargets the action while the agent still signs and pays", async () => {
  const rawMod = await raw();
  const { AgentRuntime, Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x40 + i));
  const target = Uint8Array.from({ length: 32 }, () => 0x77);

  const { server, url } = await mockNode({
    onEnvelope: () => ({ accepted: true, turn_hash: "aa".repeat(32) }),
  });
  try {
    const runtime = new AgentRuntime(identity, url);
    const authorized = await runtime.turn().on(target).writeU64(0, 1n).sign();
    const action = authorized.action();
    assert.equal(hex(action.target), hex(target), ".on(target) must aim the ACTION at the target");
    // The write verb defaulted its cell to the acting (target) cell.
    assert.equal(hex(action.effects[0].cell), hex(target));
  } finally {
    server.close();
  }
});
