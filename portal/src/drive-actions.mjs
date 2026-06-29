/**
 * The portal's drive actions — the real, cap-gated turns the interactive portal
 * fires. Each is a thin call into the published `@dregg/sdk`: build verbs →
 * `.sign()` (Ed25519 over the canonical federation-bound message) → `.submit()`
 * (postcard `SignedTurn` to the node's `/api/turns/submit-signed` ingress) →
 * `Receipt`. No turn is mocked; the executor's gates apply identically.
 *
 * This module is imported by BOTH the browser bundle (`drive-ui.mjs`) and the
 * node round-trip test (`test/drive.test.mjs`), so the exact code the portal
 * runs is the code under test. It imports only from `@dregg/sdk/browser` (the
 * browser-clean acting surface) plus `@noble/hashes/blake3` for content
 * addressing (the same blake3 dregg commits with).
 */

import { hexEncode } from "@dregg/sdk/browser";
import { blake3 } from "@noble/hashes/blake3";

/** The cell-field slot a published page's content commitment lives in — slot 0
 * of the surface cell, the `WebOfCells::publish` convention
 * (`starbridge-web-surface/src/web_of_cells.rs`): a `dregg://` fetch reads the
 * served bytes' content hash out of THIS slot and binds the bytes to it. */
export const SITE_CONTENT_SLOT = 0;

/** The durable-checkpoint slot a metered execution lease advances — mirrors the
 * SDK's `LEASE_STEP_SLOT` (slot 4, the first general-purpose slot). */
export const LEASE_STEP_SLOT = 4;

/** blake3(content) → the 32-byte content commitment a publish turn writes. The
 * page body is self-certifying: a `dregg://` fetch checks `blake3(bytes)` equals
 * this committed value before it renders a byte. */
export function siteContentHash(content) {
  const bytes = typeof content === "string" ? new TextEncoder().encode(content) : content;
  return blake3(bytes); // 32 bytes
}

/** Common shape captured for each fired turn: the anti-blind-signing reading,
 * the signed action (so the UI can show signer + per-effect terms), and the
 * committed receipt. */
async function fire(builder) {
  const authorized = await builder.sign(); // Ed25519, federation-bound; inescapable
  const explain = authorized.explain(); // total, semantics-faithful reading
  const action = authorized.action(); // the signed action (signer, effects, args)
  const receipt = await authorized.submit(); // postcard envelope → node ingress → Receipt
  return { explain, action, receipt };
}

/**
 * (c) Fire a simple turn — transfer `amount` computrons from the connected
 * identity's cell to `toHex`. One conserving `Effect::Transfer`.
 */
export async function fireTransfer(runtime, toHex, amount) {
  const to = hexToBytes(toHex);
  const out = await fire(runtime.turn().transfer(to, BigInt(amount)));
  return { ...out, kind: "transfer", verifyCellHex: runtime.cellIdHex() };
}

/**
 * (a) Publish a minisite — commit `content`'s blake3 hash into the connected
 * identity's cell at slot 0 (the `WebOfCells::publish` surface convention),
 * under the `publish` method. The cell becomes the site's sovereignty boundary;
 * its committed `content_hash` is what a `dregg://` reader binds the served
 * bytes to. Serving the matching bytes is the web-hosting layer (the live step);
 * the COMMITMENT — the trust-bearing half — is this real cap-gated turn.
 */
export async function publishMinisite(runtime, name, content) {
  const contentHash = siteContentHash(content);
  const cellHex = runtime.cellIdHex();
  const out = await fire(
    runtime
      .turn()
      .method("publish")
      .write(SITE_CONTENT_SLOT, contentHash),
  );
  return {
    ...out,
    kind: "publish",
    name: name || "(untitled)",
    contentHashHex: hexEncode(contentHash),
    siteCellHex: cellHex,
    dreggUri: `dregg://${cellHex}`,
    verifyCellHex: cellHex,
  };
}

/**
 * (b) Open + drive a metered execution lease over the connected identity's cell.
 * `lease.run()` advances the durable checkpoint (`step → step+1`, a `SetField`
 * on slot 4) — the metered transition the cell's `FieldLte ∧ Monotonic` meter
 * program gates; a run past the ceiling is refused by the executor. This is the
 * lease's distinctive verified turn (the value `fund` leg is the same conserving
 * `Transfer` rail as a plain transfer).
 */
export async function openLease(runtime, { maxSteps = 8 } = {}) {
  const leaseCell = runtime.identity.cellId(); // the agent administers its own lease cell
  const lease = runtime.execution.lease({ maxSteps, leaseCell });
  const step = await lease.run(); // metered checkpoint turn → LeaseStep { receipt, step, remaining }
  return {
    explain: `open a metered execution lease (maxSteps ${maxSteps}) and advance its durable checkpoint to step ${step.step} — a FieldLte∧Monotonic-gated SetField on slot ${LEASE_STEP_SLOT}; ${step.remaining} runs remain`,
    action: undefined,
    receipt: step.receipt,
    kind: "lease",
    maxSteps,
    step: step.step,
    remaining: step.remaining,
    verifyCellHex: runtime.cellIdHex(),
  };
}

/** Fund a lease cell — move `amount` from the connected identity into
 * `leaseCellHex` with one conserving `Effect::Transfer`. (The lease's value leg;
 * distinct from the metered `run`.) */
export async function fundLease(runtime, leaseCellHex, amount) {
  const leaseCell = hexToBytes(leaseCellHex);
  const lease = runtime.execution.lease({ maxSteps: 0, leaseCell });
  const receipt = await lease.fund(runtime.identity.cellId(), BigInt(amount));
  return { receipt, kind: "fund", verifyCellHex: leaseCellHex };
}

/** Hex (optionally 0x-prefixed) → 32-byte Uint8Array, with a friendly error. */
export function hexToBytes(hex) {
  const clean = (hex || "").trim().replace(/^0x/, "");
  if (clean.length !== 64 || /[^0-9a-fA-F]/.test(clean)) {
    throw new Error("expected a 32-byte (64 hex char) cell id");
  }
  const out = new Uint8Array(32);
  for (let i = 0; i < 32; i++) out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  return out;
}
