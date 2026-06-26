#!/usr/bin/env node
// HEADLINE FLOW 4 — an attested query (the light-client read surface).
//
//   The read-only twin of the acting runtime: no identity, no signing. Fetch
//   the federation-attested state roots, the latest finalized checkpoint, and
//   a committed turn's full-turn STARK. (Verifying the STARK is a Rust/wasm
//   op — pure TS surfaces the bytes to verify elsewhere. See the module's
//   "Honest scope".)
//
//   node examples/attested-query.mjs [turnHashHex]
//
// Environment:
//   DREGG_NODE_URL    (default http://localhost:8421)
//
// Build first: npm run build

import { AttestedQuery } from "../dist/index.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "http://localhost:8421";

const aq = new AttestedQuery(NODE_URL);

// The federation-signed state roots — the `signatures` count is the trust
// signal (this client surfaces it; threshold-sig verification is a named TS
// follow-up).
const roots = await aq.attestedRoots();
console.log(`attested roots: ${roots.length}`);
for (const r of roots.slice(-3)) {
  console.log(`  height ${r.height}  root ${r.merkle_root.slice(0, 16)}…  sigs ${r.signatures}`);
}

// The latest finalized checkpoint.
const cp = await aq.checkpoint();
console.log("\nlatest checkpoint:");
console.log("  height:", cp.height, "epoch:", cp.epoch);
console.log("  ledger root:", cp.ledger_state_root.slice(0, 16) + "…");
console.log("  qc votes:", cp.qc_votes, "of", cp.federation_members, "members");

// A committed turn's STARK proof bytes (verify with @dregg/sdk/wasm or Rust).
const turnHash = process.argv[2];
if (turnHash) {
  const proof = await aq.turnProof(turnHash);
  if (proof) {
    console.log(`\nfull-turn STARK for ${turnHash.slice(0, 16)}…: ${proof.bytes.length} bytes`);
    console.log("  (verify with verify_full_turn — not done in pure TS)");
  } else {
    console.log(`\nno proof yet for ${turnHash.slice(0, 16)}… (the prove pool is async)`);
  }
}
