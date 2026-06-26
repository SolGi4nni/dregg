#!/usr/bin/env node
// The whole SDK in one sitting, against the live devnet:
//
//   profile → identity → faucet → authorized turn → receipt → event stream
//
//   node examples/devnet-walkthrough.mjs
//
// Environment:
//   DREGG_NODE_URL    (default http://localhost:8421)
//   DREGG_DEVNET_KEY  (if the devnet gate requires one)
//   DREGG_HOME        (profile store; defaults to ~/.dregg)
//
// Build first: npm run build

import { AgentRuntime, Identity, NodeClient, ReceiptFilter, profiles } from "../dist/index.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "http://localhost:8421";
const PROFILE = "walkthrough";

// ── 1. A named identity (the shared $DREGG_HOME/profiles store) ────────────
let identity;
try {
  identity = profiles.load(PROFILE);
  console.log(`profile ${JSON.stringify(PROFILE)} loaded`);
} catch {
  const info = profiles.create(PROFILE);
  console.log(`profile ${JSON.stringify(PROFILE)} created (pub ${info.publicKeyHex.slice(0, 16)}…)`);
  identity = profiles.load(PROFILE);
}
console.log(`agent cell: ${identity.cellIdHex()}`);

// ── 2. Bind to the node ─────────────────────────────────────────────────────
const node = new NodeClient(NODE_URL, { devnetKey: process.env.DREGG_DEVNET_KEY });
const runtime = new AgentRuntime(identity, node);

// ── 3. Faucet: materialize the agent cell with its REAL owner key ──────────
// (Required once — a cell without its Ed25519 key fails turn authorization.)
await runtime.faucet(2000);
const cell = await node.cell(identity.cellId());
console.log(`faucet ok — balance ${cell.balance}, nonce ${cell.nonce}`);

// ── 4. Subscribe BEFORE acting, so we observe our own commit ────────────────
const stream = node.events().subscribe(new ReceiptFilter().cell(identity.cellId()));

// ── 5. The one public turn shape: verbs → sign → explain → submit ──────────
// The fee is the computron BUDGET; the agent cell must hold ≥ fee, so size
// it to the faucet grant (the default 10 000 mirrors the Rust SDK).
const authorized = await runtime.turn().writeU64(0, 42n).fee(1000).sign();

// The anti-blind-signing reading: exactly what was signed, sem-tagged.
console.log("\n--- what you are about to authorize ---");
console.log(authorized.explain());
console.log("---------------------------------------\n");

let receipt;
try {
  receipt = await authorized.submit();
} catch (e) {
  if (e?.status === 401 || e?.status === 403) {
    console.error(
      "the node's signed-turn ingress is operator-gated (bearer token).\n" +
      "Set DREGG_DEVNET_KEY to the node's API token, or run against a local\n" +
      "node: dregg-node run --enable-faucet (loopback is open pre-passphrase,\n" +
      "then set-passphrase + unlock yields the token).",
    );
    process.exit(1);
  }
  throw e;
}
console.log(`committed: turn ${receipt.turnHash}`);
console.log(`  receipt ${receipt.receiptHash ?? "(pending listing)"}`);
console.log(`  finality ${receipt.finality ?? "?"} — proofless at birth: ${!receipt.hasProof()}`);

// ── 6. The same noun arrives on the nervous system ──────────────────────────
console.log("\nwaiting for the receipt on the event stream…");
const timeout = setTimeout(() => {
  console.log("(no event within 30s — closing)");
  stream.close();
}, 30_000);

for await (const observed of stream) {
  console.log(`observed: turn ${observed.turnHash} (chain index ${observed.chainIndex})`);
  if (observed.turnHash === receipt.turnHash) {
    console.log("the committed turn and the observed receipt are the same noun ✓");
    break;
  }
}
clearTimeout(timeout);
stream.close();

// ── 7. The proof attaches lazily (the node's async prove pool) ──────────────
const proof = await node.turnProof(receipt.turnHash);
if (proof) {
  receipt.attachProof(proof);
  console.log(`proof attached: ${proof.bytes.length} bytes for turn ${proof.turnHashHex.slice(0, 16)}…`);
} else {
  console.log("proof still in the prove pool — fetch later with node.turnProof(hash)");
}
