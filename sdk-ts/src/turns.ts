/**
 * The authorized turn builder — the SDK's one public turn shape.
 *
 * ```text
 * Identity → .turn() → typed verb builders → .sign() → .submit() → Receipt
 * ```
 *
 * `AgentRuntime.turn()` opens a [`TurnBuilder`]; the typed verbs
 * ([`transfer`], [`write`], [`grant`], …) accumulate the act; [`sign`] binds
 * it to the identity's Ed25519 key over the canonical signing message
 * (federation-bound, replay-separated); and [`AuthorizedTurn.submit`]
 * executes it on the node and returns the [`Receipt`] noun.
 *
 * **An unauthorized act is inexpressible here.** No method on this surface
 * yields an unsigned action — by the time anything reaches the node it
 * carries a real `Authorization::Signature` per action AND a `SignedTurn`
 * envelope signature over the canonical turn hash. The raw vocabulary
 * (including unauthorized construction) lives behind the sealed
 * `@dregg/sdk/raw` module.
 *
 * The anti-blind-signing affordance rides along: [`AuthorizedTurn.explain`]
 * renders the clerk's faithful, total explanation of exactly what was
 * signed.
 *
 * Difference from the Rust builder: there is no `.as_cell(..)` here — the
 * remote signed ingress pins `turn.agent` to the signer's default cell
 * (node/src/api.rs `post_submit_signed_turn`), so a cell-agent turn cannot
 * be expressed over this transport. `.on(target)` (act on another cell the
 * identity administers, signature verified against the target's
 * `owner_pubkey`) works as in Rust.
 */

import type { AgentRuntime } from "./client";
import { Receipt } from "./receipt";
import { explainAction } from "./explain";
import type { Action, Bytes32, CapabilityRef, CellId, Effect, Turn } from "./internal/wire";
import { fieldFromU64, unsignedActionNamed } from "./internal/wire";

/** The canonical `Payable` `pay` method name (mirrors `dregg_payable::PAY_METHOD`). */
export const PAY_METHOD = "pay";

/** Default computron budget when `.fee()` is not called (Rust parity). */
const DEFAULT_FEE = 10_000n;

/** Turn validity horizon stamped on submitted turns (seconds). */
const VALIDITY_HORIZON_SECS = 3600n;

/** Refusal to sign a meaningless turn, mirroring the Rust builder. */
export class EmptyTurnError extends Error {
  constructor() {
    super("refusing to sign an empty turn (no effects staged)");
    this.name = "EmptyTurnError";
  }
}

/**
 * The typed verb builder. Open one with `runtime.turn()`; finish with
 * [`sign`].
 */
export class TurnBuilder {
  private readonly runtime: AgentRuntime;
  /** `undefined` = ordinary agent turn; a CellId = the `.on(target)` shape. */
  private actingOn: CellId | undefined;
  private methodName = "execute";
  private effectList: Effect[] = [];
  private argList: Bytes32[] = [];
  private feeValue: bigint | undefined;

  constructor(runtime: AgentRuntime) {
    this.runtime = runtime;
  }

  /** The cell whose authority this turn exercises. */
  private actingCell(): CellId {
    return this.actingOn ?? this.runtime.identity.cellId();
  }

  /**
   * Target another cell the identity administers (the action targets
   * `target`; this agent signs and pays). The node verifies the signature
   * against `target`'s `owner_pubkey` and requires the agent's c-list
   * capability on it.
   */
  on(target: CellId): this {
    this.actingOn = target;
    return this;
  }

  /** Set the action's method verb (default `"execute"`). */
  method(name: string): this {
    this.methodName = name;
    return this;
  }

  /** Set the turn fee (computron budget). Defaults to 10 000. */
  fee(fee: number | bigint): this {
    this.feeValue = BigInt(fee);
    return this;
  }

  // ─── typed verbs ───

  /** Transfer `amount` computrons from the acting cell to `to`. */
  transfer(to: CellId, amount: number | bigint): this {
    this.effectList.push({ kind: "transfer", from: this.actingCell(), to, amount });
    return this;
  }

  /**
   * Transfer with an explicit source cell (must still be within this
   * identity's authority — the executor checks, not the builder).
   */
  transferFrom(from: CellId, to: CellId, amount: number | bigint): this {
    this.effectList.push({ kind: "transfer", from, to, amount });
    return this;
  }

  /**
   * Write state slot `index` of the acting cell (admitted only where the
   * cell's installed program allows).
   */
  write(index: number, value: Bytes32): this {
    this.effectList.push({ kind: "setField", cell: this.actingCell(), index, value });
    return this;
  }

  /** [`write`] with a numeric value (encoded like `field_from_u64`). */
  writeU64(index: number, value: number | bigint): this {
    return this.write(index, fieldFromU64(value));
  }

  /**
   * Grant a capability from the acting cell to `to` (non-amplifying: the
   * executor admits only grants within held authority).
   */
  grant(to: CellId, cap: CapabilityRef): this {
    this.effectList.push({ kind: "grantCapability", from: this.actingCell(), to, cap });
    return this;
  }

  /** Bump the acting cell's nonce (a deliberate no-op state advance). */
  incrementNonce(): this {
    this.effectList.push({ kind: "incrementNonce", cell: this.actingCell() });
    return this;
  }

  /** Append one prebuilt effect (escape hatch; the executor's gates apply identically). */
  effect(effect: Effect): this {
    this.effectList.push(effect);
    return this;
  }

  /** Append a prebuilt effect list (the splice point for plan builders). */
  effects(effects: Iterable<Effect>): this {
    for (const e of effects) this.effectList.push(e);
    return this;
  }

  /**
   * Set the action's argument vector (the typed witness the method carries;
   * the routing/auth gate on the method symbol, these are the receipt-bound
   * record). Each entry is a 32-byte field element. Replaces any prior args.
   */
  args(args: Bytes32[]): this {
    this.argList = args.slice();
    return this;
  }

  /**
   * **`pay`** — move `amount` of `asset` from the acting cell to `to` through
   * the canonical `Payable` `pay` desugar. The byte-identical twin of
   * `dregg_payable::resolve_pay` / the Rust SDK's `AgentRuntime::pay`: the
   * action's `method` is `pay`, its `args` are `[asset, field_from_u64(amount),
   * to]` (the `pay_args` witness), and it carries EXACTLY ONE conserving
   * `Effect::Transfer` (per-asset Σδ=0). The same value rail the app
   * framework's `Payable::pay` and the metered tool-gateway charge ride — not a
   * hand-rolled effect.
   *
   * `asset` is the asset to pay in (the payer's `token_id`; a bridged `$DREGG`
   * mirror asset is an ordinary 32-byte id, routed identically).
   */
  pay(to: CellId, amount: number | bigint, asset: Bytes32): this {
    this.methodName = PAY_METHOD;
    this.argList = [asset, fieldFromU64(amount), to];
    this.effectList.push({ kind: "transfer", from: this.actingCell(), to, amount });
    return this;
  }

  // ─── terminal ───

  /**
   * Sign the built action with this identity's key over the canonical
   * federation-bound signing message, yielding an [`AuthorizedTurn`] ready
   * to [`submit`](AuthorizedTurn.submit).
   *
   * After this point the act is credentialed; there is no way back to an
   * unauthorized shape. (Async because the federation binding is discovered
   * from the node on first use.)
   */
  async sign(): Promise<AuthorizedTurn> {
    if (this.effectList.length === 0) {
      throw new EmptyTurnError();
    }
    const target = this.actingCell();
    const federationId = await this.runtime.node.federationId();
    const unsigned = unsignedActionNamed(target, this.methodName, this.effectList);
    unsigned.args = this.argList;
    // `dregg-action-sig-v3` binds the SUBMITTING turn's nonce into the action
    // signature, so the nonce must be known here. `submit()` re-signs if the
    // live counter has moved on by then (mirror of the Rust
    // `resign_full_commitment_at` repair).
    const nonce = await this.runtime.currentNonce();
    const action = this.runtime.identity.signAction(unsigned, federationId, nonce);
    return new AuthorizedTurn(
      this.runtime,
      unsigned,
      action,
      federationId,
      nonce,
      this.feeValue ?? DEFAULT_FEE,
    );
  }
}

/**
 * A signed, ready-to-submit turn. Produced by [`TurnBuilder.sign`]; consumed
 * by [`submit`](AuthorizedTurn.submit).
 */
export class AuthorizedTurn {
  private readonly runtime: AgentRuntime;
  /** The unsigned scaffold, kept so a moved nonce can be re-signed (v3). */
  private readonly unsignedAction: Action;
  private signedAction: Action;
  private readonly federationId: Uint8Array;
  /** The turn nonce `signedAction`'s signature is bound to (`sig-v3`). */
  private signedNonce: bigint;
  private readonly fee: bigint;
  private submitted = false;

  constructor(
    runtime: AgentRuntime,
    unsignedAction: Action,
    action: Action,
    federationId: Uint8Array,
    signedNonce: bigint,
    fee: bigint,
  ) {
    this.runtime = runtime;
    this.unsignedAction = unsignedAction;
    this.signedAction = action;
    this.federationId = federationId;
    this.signedNonce = signedNonce;
    this.fee = fee;
  }

  /**
   * The clerk's faithful, total explanation of exactly what was signed —
   * the anti-blind-signing reading (see `explain.ts`).
   */
  explain(): string {
    return explainAction(this.signedAction);
  }

  /** The signed action (inspection only — `submit` consumes the turn). */
  action(): Action {
    return this.signedAction;
  }

  /**
   * Execute the turn on the node and return the [`Receipt`] noun.
   *
   * The agent cell pays; the turn rides the cell's live nonce, the node's
   * receipt-chain head (`previous_receipt_hash` causal binding), and a
   * one-hour validity horizon; the envelope signature binds the canonical
   * `Turn::hash` (v3). A chain-head race (another commit landing between
   * read and submit) is retried once with fresh bindings. Because
   * `dregg-action-sig-v3` binds the turn nonce into the ACTION signature, a
   * moved nonce means the action is re-signed too — not just the envelope.
   * One-shot: a second call is refused (the consumed turn would replay-fail
   * anyway).
   */
  async submit(): Promise<Receipt> {
    if (this.submitted) {
      throw new Error("AuthorizedTurn already submitted (one-shot, like the Rust consume-on-submit)");
    }
    this.submitted = true;
    let lastError: unknown;
    for (let attempt = 0; attempt < 2; attempt++) {
      const nonce = await this.runtime.currentNonce();
      // v3: the action signature covers the turn nonce. If the live counter
      // moved since `sign()`, the banked signature is bound to a stale nonce
      // and would be rejected — re-sign over the live one.
      if (nonce !== this.signedNonce) {
        this.signedAction = this.runtime.identity.signAction(
          this.unsignedAction,
          this.federationId,
          nonce,
        );
        this.signedNonce = nonce;
      }
      const previousReceiptHash = await this.runtime.node.receiptChainHead();
      const turn: Turn = {
        agent: this.runtime.identity.cellId(),
        nonce,
        roots: [{ action: this.signedAction, children: [] }],
        fee: this.fee,
        validUntil: BigInt(Math.floor(Date.now() / 1000)) + VALIDITY_HORIZON_SECS,
        previousReceiptHash,
      };
      try {
        return await this.runtime.submitTurn(turn);
      } catch (e) {
        lastError = e;
        const msg = e instanceof Error ? e.message : String(e);
        if (attempt === 0 && /receipt chain mismatch|nonce/i.test(msg)) {
          continue; // racing commit moved the head; rebind and retry once
        }
        throw e;
      }
    }
    throw lastError;
  }
}
