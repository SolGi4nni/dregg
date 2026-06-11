/**
 * `explain` — the cipherclerk's faithful reading of a turn, in the same human
 * terms `sdk/src/explain.rs` uses.
 *
 * A turn term has three readings: it can be **executed** (the node's executor
 * walks the call forest), it can be **proved** (the circuit witnesses the same
 * evolution), and — here — it can be **explained**: a deterministic rendering
 * of exactly what the turn does, shown to the citizen BEFORE the extension
 * releases a signature. The prose per effect/authorization mirrors the SDK's
 * `explain_effect` / `auth_mode` / `explain_action` / `explain_turn` renderings
 * word-for-word, so the extension and the Rust clerk describe the same turn in
 * the same words.
 *
 * # Faithfulness binding (what differs from the Rust)
 *
 * The Rust renderer appends a per-effect/per-action `[sem <digest>]` tag from
 * `Effect::hash` / `Action::hash`. The extension does not reimplement those
 * canonical hashes in JS; instead the turn-level rendering carries
 * `[turn <hash>]` — the canonical `Turn::hash` (v3) computed by the SAME wasm
 * call that produced the signed bytes (`sign_turn_v3`'s `turn_id`). That hash
 * is the digest the node verifies the envelope signature against and the value
 * the receipt commits, so the rendering on screen is bound to exactly the term
 * that will execute: a different turn gets a different `[turn …]` tag.
 *
 * # Totality
 *
 * Every input renders to a string with no throw. JS cannot be compiler-forced
 * exhaustive over wire JSON the way the Rust `match` is, so an unrecognized
 * effect or authorization variant renders as an explicit UNKNOWN line and sets
 * `hasUnknown` — the confirm UI must surface that as "do not sign blind"
 * rather than silently eliding it.
 */

/** Render 32 bytes (JSON `number[]` from serde) as lowercase hex; total. */
export function hx32(bytes: unknown): string {
  if (!Array.isArray(bytes)) return "??";
  return bytes.map((b) => (Number(b) & 0xff).toString(16).padStart(2, "0")).join("");
}

function len(v: unknown): number {
  return Array.isArray(v) ? v.length : 0;
}

interface EffectReading {
  body: string;
  unknown: boolean;
}

/**
 * One-line human-readable summary of a single Effect's body — the prose a
 * citizen reads. Mirrors `effect_body` in sdk/src/explain.rs exactly.
 *
 * Wire shape: serde external tagging — `{ "Transfer": { ... } }` for struct
 * variants, the bare string `"RefreshDelegation"` for the unit variant.
 */
export function effectBody(effect: unknown): EffectReading {
  if (effect === "RefreshDelegation") {
    return { body: "refresh this cell's delegation snapshot from its parent", unknown: false };
  }
  if (typeof effect !== "object" || effect === null) {
    return { body: `UNKNOWN effect ${JSON.stringify(effect)} (unrecognized by this cipherclerk)`, unknown: true };
  }
  const keys = Object.keys(effect as Record<string, unknown>);
  if (keys.length !== 1) {
    return { body: `UNKNOWN effect shape (${keys.length} tags)`, unknown: true };
  }
  const tag = keys[0];
  const e = (effect as Record<string, Record<string, unknown>>)[tag] ?? {};
  const body = ((): string | null => {
    switch (tag) {
      case "SetField":
        return `set state field #${e.index} of cell ${hx32(e.cell)} to 0x${hx32(e.value)}`;
      case "Transfer":
        return `transfer ${e.amount} computrons from cell ${hx32(e.from)} to cell ${hx32(e.to)}`;
      case "GrantCapability": {
        const cap = (e.cap ?? {}) as Record<string, unknown>;
        return `grant capability (target ${hx32(cap.target)} slot ${cap.slot}) from cell ${hx32(e.from)} to cell ${hx32(e.to)}`;
      }
      case "RevokeCapability":
        return `revoke capability in slot ${e.slot} of cell ${hx32(e.cell)}`;
      case "EmitEvent": {
        const ev = (e.event ?? {}) as Record<string, unknown>;
        return `emit event (topic 0x${hx32(ev.topic)}, ${len(ev.data)} data field(s)) from cell ${hx32(e.cell)}`;
      }
      case "IncrementNonce":
        return `increment the nonce of cell ${hx32(e.cell)}`;
      case "CreateCell":
        return `create a new cell (owner 0x${hx32(e.public_key)}, token 0x${hx32(e.token_id)}) with balance ${e.balance}`;
      case "SetPermissions":
        return `set the permissions of cell ${hx32(e.cell)} (applied last in the action)`;
      case "SetVerificationKey":
        return `set the verification key of cell ${hx32(e.cell)} to ${e.new_vk != null ? "a key" : "none"} (applied last in the action)`;
      case "NoteSpend":
        return `spend a private note (value ${e.value}, asset ${e.asset_type})`;
      case "NoteCreate":
        return `create a private note (value ${e.value}, asset ${e.asset_type})`;
      case "SpawnWithDelegation":
        return `spawn a child cell (owner 0x${hx32(e.child_public_key)}) with a delegation snapshot (max staleness ${e.max_staleness}s)`;
      case "RefreshDelegation":
        return "refresh this cell's delegation snapshot from its parent";
      case "RevokeDelegation":
        return `revoke delegation to child cell ${hx32(e.child)} (by bumping the parent epoch)`;
      case "BridgeMint":
        return "mint a note locally from a portable cross-federation spend proof";
      case "Introduce":
        return `introduce cell ${hx32(e.introducer)} to cell ${hx32(e.recipient)} on target cell ${hx32(e.target)}`;
      case "PipelinedSend": {
        const action = (e.action ?? {}) as Record<string, unknown>;
        return `pipeline a send to an eventual ref, carrying ${len(action.effects)} sub-effect(s)`;
      }
      case "ExerciseViaCapability":
        return `exercise the capability in slot ${e.cap_slot}, performing ${len(e.inner_effects)} inner effect(s)`;
      case "MakeSovereign":
        return `make cell ${hx32(e.cell)} sovereign (store only its state commitment)`;
      case "CreateCellFromFactory":
        return `create a cell from factory 0x${hx32(e.factory_vk)} (owner 0x${hx32(e.owner_pubkey)}, token 0x${hx32(e.token_id)})`;
      case "Refusal":
        return `record a refusal on cell ${hx32(e.cell)} of offered action 0x${hx32(e.offered_action_commitment)}`;
      case "CellSeal":
        return `seal cell ${hx32(e.target)} (reason commitment 0x${hx32(e.reason)})`;
      case "CellUnseal":
        return `unseal cell ${hx32(e.target)} (return it to live)`;
      case "CellDestroy":
        return `permanently destroy cell ${hx32(e.target)} (bind its death certificate)`;
      case "Burn":
        return `burn ${e.amount} from slot ${e.slot} of cell ${hx32(e.target)} (supply reduced, disclosed)`;
      case "AttenuateCapability":
        return `narrow (attenuate) the capability in slot ${e.slot} of cell ${hx32(e.cell)}`;
      case "ReceiptArchive":
        return `archive this cell's receipt-chain prefix up to height ${e.prefix_end_height}`;
      default:
        return null;
    }
  })();
  if (body === null) {
    return { body: `UNKNOWN effect "${tag}" (unrecognized by this cipherclerk — do not sign blind)`, unknown: true };
  }
  return { body, unknown: false };
}

/**
 * Render the Authorization mode of an action (the *how-authorized* reading).
 * Mirrors `auth_mode` in sdk/src/explain.rs. Wire shape: external tagging —
 * `"Unchecked"` for the unit variant, `{ "Signature": [...] }` etc otherwise.
 */
export function authMode(auth: unknown): { mode: string; unknown: boolean } {
  const tag =
    typeof auth === "string"
      ? auth
      : typeof auth === "object" && auth !== null && Object.keys(auth).length === 1
        ? Object.keys(auth)[0]
        : null;
  switch (tag) {
    case "Signature": return { mode: "an Ed25519 signature", unknown: false };
    case "Proof": return { mode: "a zero-knowledge proof", unknown: false };
    case "Breadstuff": return { mode: "a capability token", unknown: false };
    case "Bearer": return { mode: "a bearer capability (delegation chain)", unknown: false };
    case "Unchecked":
    case "None": // serde alias on the wire
      return { mode: "NO authorization (unchecked — only valid if the cell permits)", unknown: false };
    case "CapTpDelivered": return { mode: "a verified CapTP delivery certificate", unknown: false };
    case "Custom": return { mode: "an app-defined witnessed predicate", unknown: false };
    case "OneOf": return { mode: "one of several candidate authorizations", unknown: false };
    case "Stealth": return { mode: "a one-time stealth key", unknown: false };
    case "Token": return { mode: "a biscuit/macaroon credential", unknown: false };
    default:
      return { mode: `UNKNOWN authorization ${JSON.stringify(tag)}`, unknown: true };
  }
}

export interface Explanation {
  text: string;
  /** True when any effect/authorization variant was unrecognized. */
  hasUnknown: boolean;
}

/**
 * Render a single Action (JSON wire shape) to a description matching
 * `explain_action` in sdk/src/explain.rs (minus the per-action `[sem]` tag —
 * see the module docs for the turn-level binding that replaces it).
 */
export function explainAction(action: unknown): Explanation {
  const a = (typeof action === "object" && action !== null ? action : {}) as Record<string, unknown>;
  const auth = authMode(a.authorization);
  let hasUnknown = auth.unknown;
  let out = `Action on cell ${hx32(a.target)}, authorized by ${auth.mode}`;
  if (a.balance_change != null) {
    out += `, balance change ${a.balance_change}`;
  }
  const effects = Array.isArray(a.effects) ? a.effects : [];
  out += `:\n  ${effects.length} effect(s):\n`;
  effects.forEach((effect, i) => {
    const r = effectBody(effect);
    hasUnknown = hasUnknown || r.unknown;
    out += `    ${i + 1}. ${r.body}\n`;
  });
  return { text: out, hasUnknown };
}

/** Depth-first pre-order over the call forest, matching `CallForest::iter_dfs`. */
function dfsTrees(forest: unknown): Array<Record<string, unknown>> {
  const roots =
    typeof forest === "object" && forest !== null && Array.isArray((forest as Record<string, unknown>).roots)
      ? ((forest as Record<string, unknown>).roots as Array<Record<string, unknown>>)
      : [];
  const out: Array<Record<string, unknown>> = [];
  const visit = (tree: Record<string, unknown>): void => {
    out.push(tree);
    const children = Array.isArray(tree.children) ? (tree.children as Array<Record<string, unknown>>) : [];
    for (const child of children) visit(child);
  };
  for (const root of roots) visit(root);
  return out;
}

/**
 * Render an entire Turn (JSON wire shape, e.g. `sign_turn_v3`'s
 * `turn_bytes_json`) to a faithful description: the agent, the nonce, the fee,
 * and every action in the call forest — matching `explain_turn` in
 * sdk/src/explain.rs — bound to the canonical turn hash (`turnIdHex`, the
 * `Turn::hash` v3 the node verifies and commits).
 */
export function explainTurn(turn: unknown, turnIdHex: string): Explanation {
  const t = (typeof turn === "object" && turn !== null ? turn : {}) as Record<string, unknown>;
  let out = `Turn by agent ${hx32(t.agent)} (nonce ${t.nonce}, fee ${t.fee})`;
  if (t.memo != null) {
    out += ` memo ${JSON.stringify(t.memo)}`;
  }
  out += "\n";
  const trees = dfsTrees(t.call_forest);
  out += `${trees.length} action(s) in the call forest:\n`;
  let hasUnknown = false;
  trees.forEach((tree, i) => {
    const r = explainAction(tree.action);
    hasUnknown = hasUnknown || r.hasUnknown;
    out += `[${i}] ${r.text}\n`;
  });
  out += `[turn ${turnIdHex}]`;
  return { text: out, hasUnknown };
}
