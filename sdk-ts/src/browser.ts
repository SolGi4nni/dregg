/**
 * `@dregg/sdk/browser` — the browser-safe, fetch-only organ surface.
 *
 * The full `@dregg/sdk` entry statically imports `node:crypto` (Ed25519
 * signing in `internal/ed25519`) and `fs`/`path` (the `profiles` store), so a
 * browser ESM loader cannot parse it. This entry carries ONLY the part that
 * is pure `fetch`: a faithful `BrowserNodeClient` (the same HTTP contract —
 * devnet headers, JSON + SSE) and the node-backed organ clients
 * ([`TrustlineClient`], [`ChannelsClient`]) constructed against it. The dregg
 * playground imports this entry to drive the organs in the browser.
 *
 * `BrowserNodeClient` is byte-for-byte the same wire behaviour as the main
 * `NodeClient.getJson` / `.postJson` / `.sseStream` (it is the exact same
 * request shape the organ clients call); it simply omits the signing-bound
 * methods (`.turn()`, faucet-signed flows) that need node crypto. For those,
 * and for `Identity` / `MailboxClient` / `AttestedQuery` STARK verification,
 * use the wasm path (`pkg/dregg_wasm`) or the Node entry `@dregg/sdk`.
 *
 * A named follow-up (`sdk-browser-ed25519-webcrypto`) would back `Identity`
 * with WebCrypto/@noble ed25519 and let the full acting surface bundle too.
 */

import { TrustlineClient } from "./trustline";
import { ChannelsClient } from "./channels";

// Re-export the organ clients (type-only deps on NodeClient → browser-clean).
export { TrustlineClient } from "./trustline";
export type {
  TrustlineOpened,
  TrustlineDraw,
  TrustlineRepay,
  TrustlineSettle,
  TrustlineClose,
  TrustlineStatus,
} from "./trustline";
export { ChannelsClient } from "./channels";
export type {
  MemberSpec,
  SealedEpochKey,
  ChannelStep,
  ChannelPosted,
  ChannelStatus,
  ChannelMessage,
} from "./channels";

/** Options for [`BrowserNodeClient`] — mirrors the main `NodeClientOptions`. */
export interface BrowserNodeClientOptions {
  /** The operator/devnet key for operator-gated routes (trustline/channels). */
  devnetKey?: string;
  /** Per-request timeout in ms (default 15000). */
  timeoutMs?: number;
}

/** A non-2xx node response — mirrors the main `NodeError`. */
export class NodeError extends Error {
  readonly status?: number;
  constructor(message: string, status?: number) {
    super(message);
    this.name = "NodeError";
    this.status = status;
  }
}

interface NodeIdentity {
  public_key: string;
  [k: string]: unknown;
}

/**
 * The browser-safe node client. Implements exactly the surface the organ
 * clients call — `getJson` / `postJson` / `sseStream` — plus a liveness probe
 * (`operatorPublicKeyHex`), all over `fetch`. No signing, no key material.
 */
export class BrowserNodeClient {
  readonly baseUrl: string;
  private readonly opts: BrowserNodeClientOptions;

  constructor(baseUrl: string, opts: BrowserNodeClientOptions = {}) {
    this.baseUrl = baseUrl.replace(/\/+$/, "");
    this.opts = opts;
  }

  private headers(extra: Record<string, string> = {}): Record<string, string> {
    const h: Record<string, string> = { ...extra };
    if (this.opts.devnetKey) {
      h["X-Devnet-Key"] = this.opts.devnetKey;
      h["Authorization"] = `Bearer ${this.opts.devnetKey}`;
    }
    return h;
  }

  private async request<T>(path: string, init: RequestInit = {}): Promise<T> {
    const resp = await fetch(this.baseUrl + path, {
      signal: AbortSignal.timeout(this.opts.timeoutMs ?? 15000),
      ...init,
      headers: this.headers((init.headers as Record<string, string>) ?? {}),
    });
    if (!resp.ok) {
      const body = await resp.text().catch(() => "");
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${body.slice(0, 300)}`, resp.status);
    }
    return (await resp.json()) as T;
  }

  /** `GET {path}` → parsed JSON (the organ clients' generic read). */
  getJson<T>(path: string): Promise<T> {
    return this.request<T>(path);
  }

  /** `POST {path}` with a JSON body → parsed JSON (the organ clients' write). */
  postJson<T>(path: string, body: unknown): Promise<T> {
    return this.request<T>(path, {
      method: "POST",
      body: JSON.stringify(body),
      headers: { "Content-Type": "application/json" },
    });
  }

  /** A node SSE route as a one-shot async iterable of parsed `data:` JSON. */
  async *sseStream<T>(path: string): AsyncIterable<T> {
    const resp = await fetch(this.baseUrl + path, {
      headers: this.headers({ Accept: "text/event-stream" }),
    });
    if (!resp.ok || !resp.body) {
      const txt = resp.body ? await resp.text().catch(() => "") : "";
      throw new NodeError(`HTTP ${resp.status} from ${path}: ${txt.slice(0, 300)}`, resp.status);
    }
    const reader = resp.body.getReader();
    const decoder = new TextDecoder();
    let buf = "";
    for (;;) {
      const { value, done } = await reader.read();
      if (done) break;
      buf += decoder.decode(value, { stream: true });
      let idx: number;
      while ((idx = buf.indexOf("\n\n")) >= 0) {
        const frame = buf.slice(0, idx);
        buf = buf.slice(idx + 2);
        for (const line of frame.split("\n")) {
          if (line.startsWith("data:")) {
            const data = line.slice(5).trim();
            if (data) yield JSON.parse(data) as T;
          }
        }
      }
    }
  }

  /**
   * The node operator's Ed25519 public key (hex). `GET /api/node/identity`,
   * falling back to `/status` for older node builds. Doubles as a liveness
   * probe. Mirrors the main `NodeClient.operatorPublicKeyHex`.
   */
  async operatorPublicKeyHex(): Promise<string> {
    try {
      return (await this.request<NodeIdentity>("/api/node/identity")).public_key;
    } catch (e) {
      if (e instanceof NodeError && e.status === 404) {
        return (await this.request<{ public_key: string }>("/status")).public_key;
      }
      throw e;
    }
  }

  /** The **trustline** organ (`docs/ORGANS.md` §1). Operator-gated. */
  trustline(): TrustlineClient {
    // The organ client only duck-types getJson/postJson; this is faithful.
    return new TrustlineClient(this as unknown as never);
  }

  /** The **channels** organ (`docs/ORGANS.md` §4). Operator-gated. */
  channels(): ChannelsClient {
    return new ChannelsClient(this as unknown as never);
  }
}
