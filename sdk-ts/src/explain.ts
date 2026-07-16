/**
 * `explain` — the cipherclerk's third reading of a turn (the clerk that
 * cannot misstate what a turn does). A turn term can be **executed**,
 * **proved**, and — here — **explained**: a deterministic rendering of
 * exactly what it does, shown before authorizing. The description on the
 * screen is another reading of the very term that executes, not a caption
 * that can drift.
 *
 * Guarantees (mirroring `sdk/src/explain.rs`):
 *
 * 1. **Totality.** Every modeled `Effect`, `Action`, and `Turn` renders with
 *    no throw. The per-effect switch is exhaustive (a `never` check makes
 *    adding a TS effect variant without a reading a compile error, the same
 *    discipline as Rust's no-`_ =>` match).
 *
 * 2. **Injectivity-on-semantics.** Each rendering carries a canonical
 *    `[sem <digest>]` tag derived from the term's own canonical BLAKE3 hash
 *    (the SAME digest the Rust executor and circuit bind — `Effect::hash` /
 *    `Action::hash`), so two renderings that are textually equal have equal
 *    semantics: the screen cannot show identical text for two turns that
 *    would do different things.
 *
 * NOT claimed: that the prose is a correct natural-language account of
 * intent — only that no other turn renders to the same string unless it has
 * the same semantics.
 */

import { hexEncode } from "./internal/bytes";
import type { Action, Authorization, Effect, Turn } from "./internal/wire";
import { actionHash, effectHash } from "./internal/wire";

const hx32 = (b: Uint8Array): string => hexEncode(b);

/** The faithfulness-carrying suffix: equal tag ⇒ equal canonical hash. */
function semTag(hash: Uint8Array): string {
  return `[sem ${hx32(hash)}]`;
}

/** The structural prose of one effect (same terms as `sdk/src/explain.rs`). */
function effectBody(effect: Effect): string {
  switch (effect.kind) {
    case "setField":
      return `set state field #${effect.index} of cell ${hx32(effect.cell)} to 0x${hx32(effect.value)}`;
    case "transfer":
      return `transfer ${effect.amount} computrons from cell ${hx32(effect.from)} to cell ${hx32(effect.to)}`;
    case "grantCapability":
      return `grant capability (target ${hx32(effect.cap.target)} slot ${effect.cap.slot}) from cell ${hx32(effect.from)} to cell ${hx32(effect.to)}`;
    case "revokeCapability":
      return `revoke capability in slot ${effect.slot} of cell ${hx32(effect.cell)}`;
    case "emitEvent":
      return `emit event (topic 0x${hx32(effect.topic)}, ${effect.data.length} data field(s)) from cell ${hx32(effect.cell)}`;
    case "incrementNonce":
      return `increment the nonce of cell ${hx32(effect.cell)}`;
    case "createCell":
      return `create a new cell (owner 0x${hx32(effect.publicKey)}, token 0x${hx32(effect.tokenId)}) with balance ${effect.balance}`;
    default: {
      // Exhaustiveness tooth: a new Effect variant without a reading is a
      // compile error here, mirroring the Rust no-default-arm match.
      const unreachable: never = effect;
      return unreachable;
    }
  }
}

/**
 * Render a single effect to a faithful, total description: the prose body
 * followed by the canonical `[sem <digest>]` tag from `Effect::hash`.
 */
export function explainEffect(effect: Effect): string {
  return `${effectBody(effect)} ${semTag(effectHash(effect))}`;
}

/** The *how-authorized* reading. Total over the modeled variants. */
function authMode(auth: Authorization): string {
  switch (auth.kind) {
    case "signature":
      return "an Ed25519 signature (classical only — no post-quantum half)";
    case "hybridSignature":
      return auth.mlDsa.length > 0
        ? "a HYBRID signature (Ed25519 + ML-DSA-65 post-quantum; both halves must verify)"
        : "a HYBRID signature with the post-quantum half ABSENT (Ed25519 alone — rejected once the node requires PQ)";
    case "unchecked":
      return "NO authorization (unchecked — only valid if the cell permits)";
    default: {
      const unreachable: never = auth;
      return unreachable;
    }
  }
}

/**
 * Render a single action: target cell, authorization mode, each effect's
 * reading, and the action-level `[sem <digest>]` tag from `Action::hash`
 * (which binds target, method, args, authorization, effects, modes,
 * balance change, and witness blobs).
 */
export function explainAction(action: Action): string {
  let out = `Action on cell ${hx32(action.target)}, authorized by ${authMode(action.authorization)}`;
  if (action.balanceChange !== undefined) {
    out += `, balance change ${action.balanceChange}`;
  }
  out += `:\n  ${action.effects.length} effect(s):\n`;
  action.effects.forEach((effect, i) => {
    out += `    ${i + 1}. ${explainEffect(effect)}\n`;
  });
  out += `  ${semTag(actionHash(action))}`;
  return out;
}

/**
 * Render an entire turn: the agent, the nonce, the fee, and every action in
 * the call forest (depth-first pre-order), each carrying its own `[sem]`.
 */
export function explainTurn(turn: Turn): string {
  let out = `Turn by agent ${hx32(turn.agent)} (nonce ${turn.nonce}, fee ${turn.fee})`;
  if (turn.memo !== undefined) {
    out += ` memo ${JSON.stringify(turn.memo)}`;
  }
  out += "\n";
  const actions: Action[] = [];
  const walk = (trees: { action: Action; children: { action: Action; children: unknown[] }[] }[]): void => {
    for (const t of trees) {
      actions.push(t.action);
      walk(t.children as never);
    }
  };
  walk(turn.roots as never);
  out += `${actions.length} action(s) in the call forest:\n`;
  actions.forEach((a, i) => {
    out += `[${i}] ${explainAction(a)}\n`;
  });
  return out;
}

/** Alias of [`explainTurn`] — the `renderTurn(turn)` reading surface. */
export const renderTurn = explainTurn;
