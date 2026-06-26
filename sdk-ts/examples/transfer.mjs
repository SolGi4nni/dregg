#!/usr/bin/env node
// HEADLINE FLOW 1 — a transfer.
//
//   identity → faucet → .turn().transfer(..).sign().submit() → Receipt
//
//   node examples/transfer.mjs
//
// Environment:
//   DREGG_NODE_URL    (default http://localhost:8421)
//   DREGG_DEVNET_KEY  (if the devnet ingress is gated)
//
// Build first: npm run build

import { AgentRuntime, Identity, NodeClient } from "../dist/index.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "http://localhost:8421";

const node = new NodeClient(NODE_URL, { devnetKey: process.env.DREGG_DEVNET_KEY });

// Two fresh identities: a sender and a recipient.
const sender = Identity.generate();
const recipient = Identity.generate();
const runtime = new AgentRuntime(sender, node);

console.log("sender   ", sender.cellIdHex());
console.log("recipient", recipient.cellIdHex());

// Materialize + fund both agent cells (devnet faucet).
await runtime.faucet(2000);
await node.faucet(recipient.cellId(), 0, recipient.publicKey); // materialize the recipient cell

// Build → read → sign → submit. The recipient cell is the transfer target.
const signed = await runtime.turn().transfer(recipient.cellId(), 500n).sign();
console.log("\n--- what you are signing ---");
console.log(signed.explain()); // the anti-blind-signing reading

const receipt = await signed.submit();
console.log("\ncommitted turn:", receipt.turnHash);
console.log("receipt hash:  ", receipt.receiptHash ?? "(pending listing)");
