// THE BROWSER FRONT DOOR (N14) — the full acting surface from `@dregg/sdk/browser`.
//
//   Identity → .turn() → .sign() → .submit() → Receipt — entirely browser-safe.
//
// This is the `sdk-browser-ed25519-webcrypto` follow-up landed
// (`docs/design-frontiers/WEB-FORWARD.md §8 S5`): `Identity` is backed by
// @noble/ed25519 (byte-identical to the old node:crypto path — the golden vector
// pins it), so the SAME two-noun front door the Node SDK uses now bundles for a
// browser tab. Drop `dist/browser.mjs` (or `@dregg/sdk/browser`) into a page, and
// a `.turn()` against the devnet is a REAL Ed25519-signed turn.
//
// Run under Node to smoke-test the surface (it runs in a tab unchanged):
//   npm run build && node examples/browser-front-door.mjs
//
// In a browser:
//   <script type="module">
//     import { Identity, AgentRuntime } from "https://unpkg.com/@dregg/sdk/dist/browser.mjs";
//     // ...same code as below...
//   </script>
//
// Environment (Node smoke-test only):
//   DREGG_NODE_URL    (default http://localhost:8421)
//   DREGG_DEVNET_KEY  (if the devnet ingress is gated)

import { AgentRuntime, Identity } from "../dist/browser.mjs";

const NODE_URL = process.env.DREGG_NODE_URL ?? "http://localhost:8421";

// Identity.generate() uses globalThis.crypto.getRandomValues — the SAME in Node
// and the browser. No node:crypto, no native dependency.
const alice = Identity.generate();
const bob = Identity.generate();

// AgentRuntime accepts a node URL directly (it builds a fetch-based NodeClient).
const runtime = new AgentRuntime(alice, NODE_URL, { devnetKey: process.env.DREGG_DEVNET_KEY });

console.log("alice (signer):", alice.cellIdHex());
console.log("bob   (target):", bob.cellIdHex());

// Build → read → sign → submit. Authorization is INESCAPABLE: there is no
// Unchecked constructor on this surface; `.sign()` stamps a real Ed25519
// signature (via @noble) before `.submit()` ever runs.
const signed = await runtime.turn().transfer(bob.cellId(), 100n).sign();

console.log("\n--- what you are signing (anti-blind-signing reading) ---");
console.log(signed.explain());

// `.submit()` is the only path to the wire — and it carries a genuine signature.
// (Against a live devnet this requires the cells to be funded/materialized; the
// point here is the SURFACE: this whole flow bundles + runs in a browser tab.)
const receipt = await signed.submit().catch((e) => ({ error: String(e) }));
console.log("\nsubmit →", receipt.turnHash ? `committed ${receipt.turnHash}` : receipt.error);
