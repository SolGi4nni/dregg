#!/usr/bin/env node
// HEADLINE FLOW 3 — a channel: create + post + remove (ORGANS §4).
//
//   A group is a cell; the membership root, key epoch, and key commitment
//   live on-cell. remove(m) darkens m's forward-read ability AND their
//   group-held capabilities in ONE atomic epoch step — the keystone.
//
//   The node runs the unified epoch-step turns (operator-gated), and returns
//   the sealed epoch-key fan-out for you to deliver. Message BODIES never
//   touch the chain: you encrypt under the current key and post only
//   ciphertext. (Sealing/opening live in @dregg/sdk/wasm or the Rust SDK —
//   this flow uses placeholder ciphertext to show the transport shape.)
//
//   node examples/channel.mjs
//
// Environment:
//   DREGG_NODE_URL    (default http://localhost:8421)
//   DREGG_DEVNET_KEY  (REQUIRED — the channels service is operator-gated)
//
// Build first: npm run build

import { Identity, NodeClient } from "../dist/index.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "http://localhost:8421";

const node = new NodeClient(NODE_URL, { devnetKey: process.env.DREGG_DEVNET_KEY });
const ch = node.channels();

// Two founding members. The seal_pk is each member's X25519 public key; here
// we reuse the Ed25519 pubkey bytes purely to exercise the wire shape.
const alice = Identity.generate();
const bob = Identity.generate();
for (const id of [alice, bob]) await node.faucet(id.cellId(), 0, id.publicKey);

const group = await ch.create(7, [
  { cell: alice.cellId(), sealPk: alice.publicKey },
  { cell: bob.cellId(), sealPk: bob.publicKey },
]);
console.log("channel:", group.channel);
console.log("epoch:", group.epoch, "members:", group.members);
console.log("sealed epoch keys (one per member):", group.fan_out.length);

// Post a body — only nonce + ciphertext go over the wire (encrypt these
// under the epoch key client-side in real use).
const nonce = crypto.getRandomValues(new Uint8Array(12));
const ciphertext = new TextEncoder().encode("hello group (would be AEAD ciphertext)");
const posted = await ch.post(group.channel, group.epoch, nonce, ciphertext);
console.log("\nposted seq", posted.seq, "at epoch", posted.epoch);

// Remove bob — ONE epoch step. He is absent from the new fan-out and his
// group-held caps stale on the freshness check.
const afterRemove = await ch.remove(group.channel, bob.cellId());
console.log("\nremoved bob → epoch", afterRemove.epoch, "members", afterRemove.members);
console.log("new fan-out excludes bob:", !afterRemove.fan_out.some((k) => k.member === bob.cellIdHex()));

const status = await ch.status(group.channel);
console.log("epochs unified (the keystone invariant):", status.epochs_unified);
