#!/usr/bin/env node
// HEADLINE FLOW 2 — a trustline: open + draw (ORGANS §1).
//
//   "Issuer extends holder a line of N" — an attenuated capability whose
//   exercise debits a shared counter. The node births the per-line cell
//   (the operator IS the issuer), so this flow is operator-gated:
//   pass DREGG_DEVNET_KEY.
//
//   node examples/trustline.mjs <holderCellHex>
//
// Environment:
//   DREGG_NODE_URL    (default https://devnet.dregg.fg-goose.online)
//   DREGG_DEVNET_KEY  (REQUIRED — the trustline service is operator-gated)
//
// Build first: npm run build

import { Identity, NodeClient } from "../dist/index.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "https://devnet.dregg.fg-goose.online";

const node = new NodeClient(NODE_URL, { devnetKey: process.env.DREGG_DEVNET_KEY });
const tl = node.trustline();

// The holder (counterparty) — pass a real cell id, or a fresh demo one.
const holder = process.argv[2] ?? Identity.generate().cellIdHex();
console.log("holder:", holder);

// Open the line: the four-turn funded birth (escrows N in full).
const line = await tl.open(holder, 1000n);
console.log("\ntrustline:", line.trustline);
console.log("line escrowed:", line.escrow, "computrons");
console.log("birth turns:", line.turn_hashes.length);

// Draw against it — the shared counter debits; the cell program enforces
// drawn ≤ ceiling for life.
const draw = await tl.draw(line.trustline, 250n);
console.log("\ndrew:", draw.amount, "→ drawn", draw.drawn, "remaining", draw.remaining);
console.log("draw digest (one-shot):", draw.digest.slice(0, 16) + "…");

// The live position.
const status = await tl.status(line.trustline);
console.log("\nposition:", JSON.stringify(
  { line: status.line, drawn: status.drawn, remaining: status.remaining, escrow: status.escrow, open: status.open },
));
