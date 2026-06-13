/**
 * **Mailbox** — a hosted inbox over the relay (`docs/ORGANS.md` §2).
 *
 * The relay is a store-and-forward service: senders enqueue sealed bodies to
 * your inbox; you drain them with a custody proof. The relay sees only
 * ciphertext. Unlike the trustline/channels services (operator-local on the
 * node), the relay is a SEPARATE network-facing service on its own port
 * (default `:3100`, `node/src/relay_service.rs`), so this client takes its
 * own base URL.
 *
 * Inbox membership operations ([`subscribe`] / [`unsubscribe`] / [`drain`])
 * are authenticated by an Ed25519 signature from the inbox OWNER over a
 * domain-separated `(owner, nonce[, max])` tuple — this client signs them
 * with your [`Identity`]. Sending ([`send`]) is unauthenticated (anyone may
 * deposit a sealed body, paying the deposit).
 *
 * ## Honest scope (the seal + the custody proof)
 *
 * - **Sealing** (encrypting a body to the recipient's X25519 key) and
 *   **opening** are NOT done here — the TS wire layer carries no X25519 /
 *   ChaCha20 machinery. You bring already-sealed ciphertext to [`send`] and
 *   open drained bodies yourself (or via `@dregg/sdk/wasm`). The relay only
 *   moves opaque bytes.
 * - **Custody**: every drained message arrives with the full
 *   `DequeueProof` (old/new roots + remaining leaves + the entry's
 *   `content_hash`). The Rust crank VERIFIES it against the queue's own
 *   verifier; this client SURFACES the proof fields on [`DrainedMessage`] but
 *   does not yet re-run the Merkle verifier in TS (a named follow-up —
 *   `mailbox-verify-dequeue-proof-in-ts`). You MUST recompute the body's
 *   `content_hash` and compare before trusting a body either way.
 *
 * ```ts
 * const mb = new MailboxClient("http://relay.example:3100", identity);
 * await mb.subscribe();                       // create your hosted inbox
 * // … a sender elsewhere: mb2.send(myPubkeyHex, sealedCiphertext, 100) …
 * const { messages } = await mb.drain(50);    // custody-proofed batch
 * await mb.unsubscribe();
 * ```
 */

import type { Identity } from "./identity";
import { hexEncode, u64le } from "./internal/bytes";

const SUBSCRIBE_DOMAIN = new TextEncoder().encode("dregg-relay-subscribe-v1");
const UNSUBSCRIBE_DOMAIN = new TextEncoder().encode("dregg-relay-unsubscribe-v1");
const DRAIN_DOMAIN = new TextEncoder().encode("dregg-relay-drain-v1");

/** Isomorphic base64 encode (Node `Buffer` or browser `btoa`). */
export function base64Encode(bytes: Uint8Array): string {
  if (typeof Buffer !== "undefined") return Buffer.from(bytes).toString("base64");
  let bin = "";
  for (const b of bytes) bin += String.fromCharCode(b);
  return btoa(bin);
}

/** Isomorphic base64 decode. */
export function base64Decode(s: string): Uint8Array {
  if (typeof Buffer !== "undefined") return Uint8Array.from(Buffer.from(s, "base64"));
  const bin = atob(s);
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}

function concat(...parts: Uint8Array[]): Uint8Array {
  const total = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}

function freshNonce(): Uint8Array {
  const n = new Uint8Array(8);
  globalThis.crypto.getRandomValues(n);
  return n;
}

/** `GET /relay/status` response. */
export interface RelayStatus {
  operator_id: string;
  bond: number;
  [extra: string]: unknown;
}

/** `POST /relay/subscribe` response. */
export interface SubscribeResult {
  owner: string;
  capacity: number;
  min_deposit: number;
  subscription_fee_paid: number;
  relay_template_hosted_inbox_root: string;
}

/** `POST /relay/send/{dest}` response. */
export interface SendResult {
  queue_root: string;
  position: number;
  relay_template_bytes_relayed_this_epoch: number;
}

/** One drained message, carrying its full dequeue (custody) proof. */
export interface DrainedMessage {
  /** The proof-covered leaf hash binding the body (hex) — recompute + compare. */
  content_hash: string;
  /** Sender public key (hex). */
  sender: string;
  deposit: number;
  enqueued_at: number;
  size: number;
  proof_old_root: string;
  proof_new_root: string;
  proof_position: number;
  /** Leaf hashes of entries remaining after this dequeue, FIFO (hex). */
  proof_remaining_leaves: string[];
  /** The ciphertext body (base64) — opaque to the relay; open it yourself. */
  payload: string;
}

/** `GET /relay/drain` response. */
export interface DrainResult {
  messages: DrainedMessage[];
  /** The inbox queue root after the batch (hex). */
  new_root: string;
}

/** `GET /relay/inbox/{id}/status` response. */
export interface InboxStatus {
  owner: string;
  pending_messages: number;
  committed_capacity: number;
  queue_root: string;
  last_drain_height: number;
  evicted: boolean;
}

/** The relay rejected a request. */
export class RelayError extends Error {
  readonly status?: number;
  constructor(message: string, status?: number) {
    super(message);
    this.name = "RelayError";
    this.status = status;
  }
}

/** Options for a [`MailboxClient`]. */
export interface MailboxClientOptions {
  /** Request timeout (ms). Default 15000. */
  timeoutMs?: number;
}

/**
 * A client for ONE owner's hosted inbox on a relay. The owner is the
 * [`Identity`] passed in; its public key is the inbox id.
 */
export class MailboxClient {
  readonly baseUrl: string;
  private readonly identity: Identity;
  private readonly opts: MailboxClientOptions;

  constructor(relayBaseUrl: string, identity: Identity, opts: MailboxClientOptions = {}) {
    this.baseUrl = relayBaseUrl.replace(/\/+$/, "");
    this.identity = identity;
    this.opts = opts;
  }

  /** The owner public key (hex) — the inbox id. */
  get ownerHex(): string {
    return this.identity.publicKeyHex;
  }

  private async request<T>(path: string, init: RequestInit = {}): Promise<T> {
    const resp = await fetch(this.baseUrl + path, {
      signal: AbortSignal.timeout(this.opts.timeoutMs ?? 15000),
      ...init,
    });
    if (!resp.ok) {
      const body = await resp.text().catch(() => "");
      throw new RelayError(`HTTP ${resp.status} from ${path}: ${body.slice(0, 300)}`, resp.status);
    }
    return (await resp.json()) as T;
  }

  /** `GET /relay/status` — the relay operator's identity + bond. */
  status(): Promise<RelayStatus> {
    return this.request<RelayStatus>("/relay/status");
  }

  /**
   * `POST /relay/subscribe` — create this owner's hosted inbox. Signs
   * `owner || nonce` under `dregg-relay-subscribe-v1`.
   */
  subscribe(capacity?: number, minDeposit?: number): Promise<SubscribeResult> {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(SUBSCRIBE_DOMAIN, owner, nonce));
    const body: Record<string, unknown> = {
      owner: this.ownerHex,
      nonce: hexEncode(nonce),
      signature: hexEncode(sig),
    };
    if (capacity !== undefined) body.capacity = capacity;
    if (minDeposit !== undefined) body.min_deposit = minDeposit;
    return this.request<SubscribeResult>("/relay/subscribe", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
    });
  }

  /**
   * `DELETE /relay/unsubscribe` — remove this owner's inbox. Signs
   * `owner || nonce` under `dregg-relay-unsubscribe-v1`.
   */
  unsubscribe(): Promise<{ success?: boolean }> {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(UNSUBSCRIBE_DOMAIN, owner, nonce));
    return this.request("/relay/unsubscribe", {
      method: "DELETE",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ owner: this.ownerHex, nonce: hexEncode(nonce), signature: hexEncode(sig) }),
    });
  }

  /**
   * `POST /relay/send/{dest}` — enqueue an ALREADY-SEALED `ciphertext` to
   * `dest`'s inbox, paying `deposit`. Unauthenticated (the sender identity
   * here only labels the message). Seal the body yourself first.
   */
  send(dest: Uint8Array | string, ciphertext: Uint8Array, deposit: number): Promise<SendResult> {
    const destHex = typeof dest === "string" ? dest : hexEncode(dest);
    return this.request<SendResult>(`/relay/send/${destHex}`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        sender: this.ownerHex,
        payload: base64Encode(ciphertext),
        deposit,
      }),
    });
  }

  /**
   * `GET /relay/drain` — drain up to `max` messages (default 100), each with
   * its full dequeue proof. Signs `owner || nonce || max_le(u64)` under
   * `dregg-relay-drain-v1`. Recompute each body's `content_hash` before
   * trusting it.
   */
  drain(max = 100): Promise<DrainResult> {
    const owner = this.identity.publicKey;
    const nonce = freshNonce();
    const sig = this.identity.signBytes(concat(DRAIN_DOMAIN, owner, nonce, u64le(max)));
    const params = new URLSearchParams({
      owner: this.ownerHex,
      nonce: hexEncode(nonce),
      max: String(max),
      signature: hexEncode(sig),
    });
    return this.request<DrainResult>(`/relay/drain?${params.toString()}`);
  }

  /** `GET /relay/inbox/{id}/status` — this inbox's queue depth + root. */
  inboxStatus(): Promise<InboxStatus> {
    return this.request<InboxStatus>(`/relay/inbox/${this.ownerHex}/status`);
  }
}
