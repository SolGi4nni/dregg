// Organ-noun surface tests (trustline / channels / mailbox / attested).
//
// No live node is required: a stub `fetch` captures the request the client
// builds (path, method, body, headers) and feeds back a canned JSON
// response, so these assert the WIRE MAPPING (route, field names, hex
// encoding) and the response shaping. The relay signature preimage is
// checked against the dregg-wasm Ed25519 oracle where possible, else by
// reconstructing the documented domain-separated message.

import { test } from "node:test";
import assert from "node:assert/strict";
import { sdk, hex, fromHex } from "./helpers.mjs";

// ── A capturing fetch stub ────────────────────────────────────────────────
function stubFetch(responder) {
  const calls = [];
  const orig = globalThis.fetch;
  globalThis.fetch = async (url, init = {}) => {
    const call = { url: String(url), init };
    calls.push(call);
    const r = responder(call) ?? { ok: true, json: {} };
    return {
      ok: r.ok ?? true,
      status: r.status ?? 200,
      body: r.body ?? null,
      async json() {
        return r.json ?? {};
      },
      async text() {
        return r.text ?? "";
      },
    };
  };
  return {
    calls,
    restore() {
      globalThis.fetch = orig;
    },
  };
}

const NODE = "https://node.example";

test("trustline: open posts the documented body + parses the response", async () => {
  const { NodeClient } = await sdk();
  const holder = "ab".repeat(32);
  const stub = stubFetch(() => ({
    json: {
      trustline: "11".repeat(32),
      issuer: "22".repeat(32),
      holder,
      line: 1000,
      escrow: 1000,
      coordinator_remaining: 1000,
      turn_hashes: ["aa", "bb", "cc", "dd"],
    },
  }));
  try {
    const node = new NodeClient(NODE, { devnetKey: "k" });
    const res = await node.trustline().open(holder, 1000n, "salt7");
    const c = stub.calls[0];
    assert.equal(c.url, `${NODE}/trustline/open`);
    assert.equal(c.init.method, "POST");
    assert.deepEqual(JSON.parse(c.init.body), { holder, line: 1000, salt: "salt7" });
    assert.equal(c.init.headers["X-Devnet-Key"], "k"); // operator-gated
    assert.equal(res.trustline, "11".repeat(32));
    assert.equal(res.turn_hashes.length, 4);
  } finally {
    stub.restore();
  }
});

test("trustline: draw/repay/status hit the right routes", async () => {
  const { NodeClient } = await sdk();
  const tl = "11".repeat(32);
  const stub = stubFetch((c) => {
    if (c.url.endsWith("/trustline/status/" + tl)) {
      return { json: { trustline: tl, line: 1000, drawn: 250, remaining: 750, open: true } };
    }
    return { json: { trustline: tl, digest: "de", amount: 250, drawn: 250, remaining: 750, coordinator_remaining: 750, turn_hash: "f0" } };
  });
  try {
    const node = new NodeClient(NODE);
    const t = node.trustline();
    const d = await t.draw(tl, 250);
    assert.equal(stub.calls[0].url, `${NODE}/trustline/draw`);
    assert.equal(d.drawn, 250);
    await t.repay(tl, 100);
    assert.equal(stub.calls[1].url, `${NODE}/trustline/repay`);
    const s = await t.status(tl);
    assert.equal(stub.calls[2].url, `${NODE}/trustline/status/${tl}`);
    assert.equal(s.remaining, 750);
  } finally {
    stub.restore();
  }
});

test("channels: create encodes members as {cell, seal_pk} hex", async () => {
  const { NodeClient } = await sdk();
  const cell = "33".repeat(32);
  const stub = stubFetch(() => ({
    json: { channel: "44".repeat(32), epoch: 1, delegation_epoch: 1, member_root: "00", key_commit: "00", members: 1, fan_out: [], turn_hashes: ["a", "b", "c", "d"] },
  }));
  try {
    const node = new NodeClient(NODE);
    const res = await node.channels().create(7, [{ cell, sealPk: fromHex("55".repeat(32)) }]);
    const c = stub.calls[0];
    assert.equal(c.url, `${NODE}/channels/create`);
    assert.deepEqual(JSON.parse(c.init.body), { tag: 7, members: [{ cell, seal_pk: "55".repeat(32) }] });
    assert.equal(res.epoch, 1);
    assert.equal(res.turn_hashes.length, 4);
  } finally {
    stub.restore();
  }
});

test("channels: post sends only nonce + ciphertext (the body never goes plaintext)", async () => {
  const { NodeClient } = await sdk();
  const channel = "44".repeat(32);
  const stub = stubFetch(() => ({ json: { channel, seq: 3, epoch: 2 } }));
  try {
    const node = new NodeClient(NODE);
    const r = await node.channels().post(channel, 2, fromHex("aabbccddeeff001122334455"), fromHex("deadbeef"));
    const body = JSON.parse(stub.calls[0].init.body);
    assert.equal(stub.calls[0].url, `${NODE}/channels/post`);
    assert.deepEqual(body, { channel, epoch: 2, nonce: "aabbccddeeff001122334455", ciphertext: "deadbeef" });
    assert.equal(r.seq, 3);
  } finally {
    stub.restore();
  }
});

test("mailbox: subscribe signs (domain || owner || nonce) — DIFFERENTIAL vs the wasm oracle's Ed25519", async () => {
  const { Identity, MailboxClient } = await sdk();
  const { loadWasmOracle } = await import("./helpers.mjs");
  const wasm = await loadWasmOracle();
  const seed = fromHex("01".repeat(32));
  const identity = Identity.fromKeyBytes(seed);
  const captured = {};
  const stub = stubFetch((c) => {
    captured.body = JSON.parse(c.init.body);
    captured.url = c.url;
    return { json: { owner: identity.publicKeyHex, capacity: 100, min_deposit: 100, subscription_fee_paid: 1000, relay_template_hosted_inbox_root: "00" } };
  });
  try {
    const mb = new MailboxClient("http://relay.example:3100", identity);
    await mb.subscribe();
    assert.equal(captured.url, "http://relay.example:3100/relay/subscribe");
    assert.equal(captured.body.owner, identity.publicKeyHex);
    // Reconstruct the signed message: domain || owner || nonce, and sign it
    // with the Rust dregg-wasm path (the source of truth). Ed25519 is
    // deterministic, so a byte-equal signature proves the TS preimage is the
    // exact one the relay verifies.
    const domain = new TextEncoder().encode("dregg-relay-subscribe-v1");
    const owner = identity.publicKey;
    const nonce = fromHex(captured.body.nonce);
    const msg = new Uint8Array(domain.length + owner.length + nonce.length);
    msg.set(domain, 0);
    msg.set(owner, domain.length);
    msg.set(nonce, domain.length + owner.length);
    const oracleSig = wasm.sign_message(seed, msg);
    assert.equal(captured.body.signature, hex(oracleSig));
  } finally {
    stub.restore();
  }
});

test("mailbox: drain signs (domain || owner || nonce || max_le) and frames query params", async () => {
  const { Identity, MailboxClient } = await sdk();
  const identity = Identity.fromKeyBytes(fromHex("02".repeat(32)));
  const stub = stubFetch(() => ({ json: { messages: [], new_root: "00".repeat(32) } }));
  try {
    const mb = new MailboxClient("http://relay.example:3100", identity);
    const res = await mb.drain(50);
    const url = new URL(stub.calls[0].url);
    assert.equal(url.pathname, "/relay/drain");
    assert.equal(url.searchParams.get("owner"), identity.publicKeyHex);
    assert.equal(url.searchParams.get("max"), "50");
    assert.ok(url.searchParams.get("signature").length === 128); // 64-byte sig hex
    assert.ok(url.searchParams.get("nonce").length === 16); // 8-byte nonce hex
    assert.deepEqual(res.messages, []);
  } finally {
    stub.restore();
  }
});

test("mailbox: base64 round-trips arbitrary bytes", async () => {
  const { base64Encode, base64Decode } = await sdk();
  const bytes = Uint8Array.from({ length: 257 }, (_, i) => (i * 37) & 0xff);
  assert.equal(hex(base64Decode(base64Encode(bytes))), hex(bytes));
});

test("attested: surfaces roots + checkpoint read routes", async () => {
  const { AttestedQuery } = await sdk();
  const stub = stubFetch((c) => {
    if (c.url.endsWith("/federation/roots")) {
      return { json: [{ height: 5, merkle_root: "ab".repeat(32), timestamp: 1, signatures: 3 }] };
    }
    return { json: { height: 5, ledger_state_root: "cd".repeat(32), note_tree_root: "00", nullifier_set_root: "00", revocation_tree_root: "00", epoch: 1, timestamp: 1, federation_members: 4, qc_votes: 3 } };
  });
  try {
    const aq = new AttestedQuery(NODE);
    const roots = await aq.attestedRoots();
    assert.equal(stub.calls[0].url, `${NODE}/federation/roots`);
    assert.equal(roots[0].signatures, 3);
    const cp = await aq.checkpoint();
    assert.equal(stub.calls[1].url, `${NODE}/checkpoint/latest`);
    assert.equal(cp.qc_votes, 3);
  } finally {
    stub.restore();
  }
});

test("the organ accessors are reachable from runtime and node", async () => {
  const { AgentRuntime, NodeClient, Identity, TrustlineClient, ChannelsClient } = await sdk();
  const node = new NodeClient(NODE);
  assert.ok(node.trustline() instanceof TrustlineClient);
  assert.ok(node.channels() instanceof ChannelsClient);
  const runtime = new AgentRuntime(Identity.fromKeyBytes(fromHex("03".repeat(32))), node);
  assert.ok(runtime.trustline() instanceof TrustlineClient);
  assert.ok(runtime.channels() instanceof ChannelsClient);
});
