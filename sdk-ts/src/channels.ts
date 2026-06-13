/**
 * **Channels** — the group-key lift as an SDK noun (`docs/ORGANS.md` §4).
 *
 * A group is a CELL: the membership commitment, the key-epoch counter, and
 * the epoch-key commitment live on-cell. Joins / removals / rekeys are
 * ordinary turns under the group's installed program. Message BODIES never
 * touch the chain — control plane on-cell, data plane ciphertext over any
 * transport.
 *
 * ## THE KEYSTONE — epoch unification
 *
 * The group's key epoch and the capability freshness epoch are THE SAME
 * counter. Every epoch-stepping operation ([`join`] / [`remove`] / [`rekey`])
 * is ONE atomic turn that bumps the membership root, the epoch, the epoch-key
 * commitment, AND the cell's `delegation_epoch` — so `remove(m)` ends, in one
 * step, BOTH m's forward-read ability (they never receive the epoch-e+1 key)
 * and m's group-held capabilities (staled by the freshness check). The
 * `epochs_unified` flag on [`ChannelStatus`] is that invariant, surfaced.
 *
 * ## Honest scope (TS face)
 *
 * The group cell's birth needs the per-group factory descriptor + the seal
 * fan-out (X25519 → HKDF → ChaCha20-Poly1305) that the Rust SDK / node
 * compute. That machinery is not in the TS wire layer, so this client drives
 * the group through the **node's channels service**
 * (`node/src/channels_service.rs`, routes `POST /channels/{create,join,
 * remove,rekey,post}` + `GET /channels/status/{cell}` + the
 * `GET /channels/messages/{cell}` SSE stream): the node computes the
 * descriptor, runs the unified epoch-step turn, and returns the sealed
 * epoch-key `fan_out` (one sealed key per current member) for you to deliver
 * over any transport. Operator-gated — pass a `devnetKey`.
 *
 * Message bodies stay client-side: you encrypt under the current epoch key
 * (the fan-out is the only place a key ever appears) and POST only
 * ciphertext + nonce to [`post`].
 *
 * ```ts
 * const ch = runtime.node.channels();
 * const g = await ch.create(7, [{ cell: aliceHex, sealPk: aliceSealHex }]);
 * await ch.join(g.channel, { cell: bobHex, sealPk: bobSealHex });   // → fresh fan_out
 * await ch.post(g.channel, g.epoch, nonceHex, ciphertextHex);       // body, ciphertext only
 * await ch.remove(g.channel, bobHex);                               // bob is darkened in ONE turn
 * for await (const m of ch.messages(g.channel)) { ... }            // SSE delivery
 * ```
 */

import type { NodeClient } from "./client";
import { hexEncode } from "./internal/bytes";
import type { CellId } from "./internal/wire";

function asHex(cell: CellId | string): string {
  return typeof cell === "string" ? cell : hexEncode(cell);
}

/** A founding/joining member: cell id + their X25519 seal public key (hex). */
export interface MemberSpec {
  cell: CellId | string;
  sealPk: Uint8Array | string;
}

/** One sealed epoch key from a step's fan-out — deliver to `member`. */
export interface SealedEpochKey {
  /** The member cell id this key is sealed to (hex). */
  member: string;
  /** The key epoch (matches the group's current `epoch`). */
  epoch: number;
  /** The sender's ephemeral X25519 public key (hex). */
  ephemeral_pk: string;
  /** The sealed epoch key (hex) — opens only with `member`'s seal secret. */
  ciphertext: string;
}

/** The response of every epoch-stepping operation (create / join / remove / rekey). */
export interface ChannelStep {
  /** The group cell id (hex). */
  channel: string;
  /** The new key epoch. */
  epoch: number;
  /** The cell's freshness epoch (equals `epoch` under the keystone). */
  delegation_epoch: number;
  /** The new openable membership commitment (hex). */
  member_root: string;
  /** The fresh epoch-key commitment (hex). */
  key_commit: string;
  /** Member count after the step. */
  members: number;
  /** One sealed epoch key per CURRENT member — deliver over any transport. */
  fan_out: SealedEpochKey[];
  /** The stepping turn hash(es); create returns all four lifecycle turns. */
  turn_hashes: string[];
}

/** `POST /channels/post` response. */
export interface ChannelPosted {
  channel: string;
  /** Monotone message sequence number assigned by the node. */
  seq: number;
  epoch: number;
}

/** `GET /channels/status/{cell}` response. */
export interface ChannelStatus {
  channel: string;
  admin: string;
  tag: string;
  epoch: number;
  delegation_epoch: number;
  /** THE INVARIANT: the key epoch and the freshness epoch agree. `false` is loud. */
  epochs_unified: boolean;
  member_root: string;
  key_commit: string;
  open: boolean;
  /** Members per the node-held roster (`null` after a restart that dropped room state). */
  members: number | null;
  messages_held: number | null;
}

/** One message off the `GET /channels/messages/{cell}` SSE stream. */
export interface ChannelMessage {
  seq: number;
  epoch: number;
  /** AEAD nonce (hex). */
  nonce: string;
  /** Ciphertext body (hex) — open it with the epoch key from the fan-out. */
  ciphertext: string;
}

function memberJson(m: MemberSpec): { cell: string; seal_pk: string } {
  return { cell: asHex(m.cell), seal_pk: typeof m.sealPk === "string" ? m.sealPk : hexEncode(m.sealPk) };
}

/**
 * The channels organ client — the ergonomic face of the node's channels
 * service. Reach it via [`NodeClient.channels`].
 */
export class ChannelsClient {
  constructor(private readonly node: NodeClient) {}

  /**
   * Birth the group at epoch 1 with `members` as founders. `tag` (u64) names
   * the group among the operator's groups. Returns the first fan-out.
   */
  create(tag: number | bigint, members: MemberSpec[]): Promise<ChannelStep> {
    return this.node.postJson<ChannelStep>("/channels/create", {
      tag: Number(tag),
      members: members.map(memberJson),
    });
  }

  /** Add a member — one unified epoch step; returns the fresh fan-out. */
  join(channel: CellId | string, member: MemberSpec): Promise<ChannelStep> {
    return this.node.postJson<ChannelStep>("/channels/join", {
      channel: asHex(channel),
      member: memberJson(member),
    });
  }

  /**
   * Remove a member — one unified epoch step that darkens BOTH their
   * forward-read ability and their group-held capabilities. The removed
   * member is simply absent from the returned fan-out.
   */
  remove(channel: CellId | string, member: CellId | string): Promise<ChannelStep> {
    return this.node.postJson<ChannelStep>("/channels/remove", {
      channel: asHex(channel),
      member: asHex(member),
    });
  }

  /** Advance the epoch without a membership change (a fresh key fan-out). */
  rekey(channel: CellId | string): Promise<ChannelStep> {
    return this.node.postJson<ChannelStep>("/channels/rekey", { channel: asHex(channel) });
  }

  /**
   * Post a message body. Encrypt client-side under the CURRENT epoch key,
   * then POST only `nonce` + `ciphertext` (hex). The body never touches the
   * chain — only this transport relay does.
   */
  post(
    channel: CellId | string,
    epoch: number | bigint,
    nonce: Uint8Array | string,
    ciphertext: Uint8Array | string,
  ): Promise<ChannelPosted> {
    return this.node.postJson<ChannelPosted>("/channels/post", {
      channel: asHex(channel),
      epoch: Number(epoch),
      nonce: typeof nonce === "string" ? nonce : hexEncode(nonce),
      ciphertext: typeof ciphertext === "string" ? ciphertext : hexEncode(ciphertext),
    });
  }

  /** Live group state: epoch, roster commitment, the `epochs_unified` tooth. */
  status(channel: CellId | string): Promise<ChannelStatus> {
    return this.node.getJson<ChannelStatus>(`/channels/status/${asHex(channel)}`);
  }

  /**
   * Subscribe to the group's message stream (`GET /channels/messages/{cell}`,
   * SSE) as an async iterable of ciphertext envelopes. Open each body with
   * the epoch key you hold from the fan-out.
   */
  async *messages(channel: CellId | string): AsyncIterable<ChannelMessage> {
    yield* this.node.sseStream<ChannelMessage>(`/channels/messages/${asHex(channel)}`);
  }
}
