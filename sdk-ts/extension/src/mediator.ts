/**
 * The trusted-path **mediator** — the security heart of the front door.
 *
 * The page ASKS; the extension + user APPROVE; the key STAYS here. This object
 * holds the dregg `Identity` (via `@dregg/sdk`'s `AgentRuntime`) and is the ONLY
 * thing that ever touches key material. A page hands it a {@link TurnRequestSpec}
 * (verbs only — no key, no signature); the mediator:
 *
 *   1. builds the turn through `AgentRuntime.turn()` (the inescapable authorized
 *      builder — there is NO `Unchecked` path on this surface);
 *   2. `.sign()`s it (a real HYBRID post-quantum signature — Ed25519 + ML-DSA-65
 *      — byte-identical to the native SDK's default signer, on the same `@noble`
 *      path the CLI/SDK pin to a golden vector);
 *   3. renders the faithful `explain()` reading + per-effect plain language and
 *      calls the injected `approve(view)` gate (the human in the loop);
 *   4. `.submit()`s ONLY if `approve` resolves true, and returns the `Receipt`.
 *
 * A refused or never-approved request is NEVER submitted and its signature never
 * leaves the mediator. The key is unreachable from the page by construction: it
 * lives behind `Identity`'s private seed, and nothing in the page protocol can
 * read, set, or derive it — the most a page learns is the public cell id and the
 * committed receipt.
 *
 * Runtime-agnostic on purpose: the MV3 service-worker wraps this with a real
 * approval popup, and the headless test wraps it with a scripted `approve` and a
 * mock node — both exercise the identical security path.
 */

import type { AgentRuntime, Receipt } from "@dregg/sdk/browser";
import { buildApprovalView } from "./explain-plain";
import { applySpec } from "./spec";
import type { ApprovalView, IdentityView, ReceiptView, TurnRequestSpec } from "./protocol";

/** The human-in-the-loop gate: shown the reading, returns the user's verdict. */
export type ApproveFn = (view: ApprovalView) => Promise<boolean>;

/** Raised when the user (or the gate) declines to approve a turn. */
export class TurnDeclinedError extends Error {
  constructor() {
    super("turn declined: the user did not approve the signing request");
    this.name = "TurnDeclinedError";
  }
}

export interface MediatorOptions {
  /** A human-readable label for the active identity (shown in the popup). */
  readonly label?: string;
}

/** Normalize a `Receipt` to the JSON view handed back to the page (no internals). */
function receiptView(r: Receipt): ReceiptView {
  return {
    turnHash: r.turnHash,
    receiptHash: r.receiptHash,
    agent: r.agent,
    postStateHash: r.postStateHash,
    computronsUsed: r.computronsUsed,
    actionCount: r.actionCount,
    finality: r.finality,
  };
}

export class TrustedPathMediator {
  private readonly runtime: AgentRuntime;
  private readonly opts: MediatorOptions;

  constructor(runtime: AgentRuntime, opts: MediatorOptions = {}) {
    this.runtime = runtime;
    this.opts = opts;
  }

  /**
   * The identity HINT a page may read — public cell id + public key only. There
   * is no method on this object that returns seed/private material; the key is
   * unreachable from here by construction.
   */
  identityView(): IdentityView {
    const id = this.runtime.identity;
    return { cellIdHex: id.cellIdHex(), publicKeyHex: id.publicKeyHex, label: this.opts.label };
  }

  /**
   * The full front-door flow for one page-requested turn: build → sign → show
   * the faithful reading → await the human gate → submit iff approved.
   *
   * Throws {@link TurnDeclinedError} (and submits nothing) when `approve`
   * resolves false. The Ed25519 signature is produced at step (2) but only
   * reaches the wire at step (4); a declined turn's signature is discarded.
   */
  async handleTurn(spec: TurnRequestSpec, approve: ApproveFn): Promise<Receipt> {
    const signer = this.runtime.identity.cellId();
    // (1)(2) Build through the inescapable authorized builder and sign.
    const builder = this.runtime.turn();
    applySpec(builder, spec, signer);
    const signed = await builder.sign(); // real hybrid PQ signature (no Unchecked path)

    // (3) The anti-blind-signing reading — derived from the SAME signed action.
    const view = buildApprovalView({
      action: signed.action(),
      origin: "", // the service-worker fills the real origin; tests pass it via spec wrapper
      signerCellIdHex: this.runtime.identity.cellIdHex(),
      pageLabel: spec.label,
    });
    const approved = await approve(view);
    if (!approved) {
      throw new TurnDeclinedError();
    }

    // (4) Only now does the signature reach the wire.
    return signed.submit();
  }

  /**
   * Like {@link handleTurn} but the caller supplies the page origin (the
   * service-worker knows it from the message sender). Keeps the origin OUT of
   * the page-controlled spec so a page cannot spoof who is asking.
   */
  async handleTurnFromOrigin(spec: TurnRequestSpec, origin: string, approve: ApproveFn): Promise<Receipt> {
    const signer = this.runtime.identity.cellId();
    const builder = this.runtime.turn();
    applySpec(builder, spec, signer);
    const signed = await builder.sign();
    const view = buildApprovalView({
      action: signed.action(),
      origin,
      signerCellIdHex: this.runtime.identity.cellIdHex(),
      pageLabel: spec.label,
    });
    if (!(await approve(view))) {
      throw new TurnDeclinedError();
    }
    return signed.submit();
  }

  /** Convenience for the read-only `dregg:turn` dry-run: build+sign, return the
   * reading WITHOUT submitting (used by tests to assert byte-identical sigs and
   * by a future popup "preview" affordance). The signature never leaves. */
  async previewTurn(spec: TurnRequestSpec, origin: string): Promise<{ view: ApprovalView; signatureHex: string }> {
    const signer = this.runtime.identity.cellId();
    const builder = this.runtime.turn();
    applySpec(builder, spec, signer);
    const signed = await builder.sign();
    const auth = signed.action().authorization;
    if (auth.kind !== "signature") throw new Error("preview: expected a signed action");
    const sig = new Uint8Array(64);
    sig.set(auth.r, 0);
    sig.set(auth.s, 32);
    const view = buildApprovalView({
      action: signed.action(),
      origin,
      signerCellIdHex: this.runtime.identity.cellIdHex(),
      pageLabel: spec.label,
    });
    let hex = "";
    for (const b of sig) hex += b.toString(16).padStart(2, "0");
    return { view, signatureHex: hex };
  }
}

export { receiptView };
