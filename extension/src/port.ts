/**
 * THE QUIET-UPGRADE PORT — the capability-shaped protocol between the in-page
 * thin view (`<dregg-poll>`) and the in-extension engine (this module, run in
 * the background/service-worker context where wasm is allowed).
 *
 * The split (DREGG-QUIET-UPGRADE.md §3) is load-bearing: NOTHING in this file
 * touches the page. It owns the wasm world, the netlayer resolve, the verify,
 * and it delegates custody consent to an injected callback that (in the
 * extension) opens the un-overlayable `confirm-intent` chrome. The element
 * never sees a key, a witness, or the wasm — only these responses, each of
 * which carries an explicit trust tier.
 *
 * This module is dependency-free (no `chrome`, no wasm import): the background
 * constructs a `PollEngine` with the real `PollWorld` constructor + a real
 * consent callback; a test constructs it with the same wasm world + an
 * auto-consent callback. Both drive the IDENTICAL engine over the IDENTICAL
 * message protocol.
 */

// ── trust tiers (§5) — never hidden, always on the wire ─────────────────────
export type TrustTier = "extension" | "sdk" | "server" | "none";

// ── the port request/response protocol (§3) ─────────────────────────────────
export type PollPortRequest =
  | { op: "resolve"; uri: string }
  | { op: "render"; uri: string }
  | { op: "fire"; uri: string; turn: string; arg: number }
  | { op: "verify"; uri: string };

export interface ResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  /** The content-addressed object's public shape (never secret state). */
  object?: { kind: string; addr: string; optionCount: number; quorum: number };
  receiptCount?: number;
  error?: string;
}

export interface RenderResponse {
  ok: boolean;
  tier: TrustTier;
  /** The world's in-wasm `render_html()` — a live tally fragment. */
  html?: string;
  optionCount?: number;
  error?: string;
}

export interface FireResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the turn was refused (below-quorum, double-vote, denied consent). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  receiptCount?: number;
  /** Re-read total across options (public tally). */
  total?: number;
  error?: string;
}

export interface VerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  receiptCount?: number;
  total?: number;
  error?: string;
}

export type PollPortResponse = ResolveResponse | RenderResponse | FireResponse | VerifyResponse;

/** The transport the element holds — a request/response channel to the engine. */
export interface PollPort {
  request(req: PollPortRequest): Promise<PollPortResponse>;
}

// ── the wasm world surface this engine needs (a structural subset) ──────────
export interface PollWorldLike {
  optionCount(): number;
  read(option: number): number;
  total(): number;
  verified(): boolean;
  receiptCount(): number;
  renderHtml(): string;
  castAs(voter: number, option: number): number;
}
export interface PollWorldCtor {
  // `quorumM` is a wasm `u64` → wasm-bindgen expects a BigInt at the boundary.
  new (numOptions: number, quorumM: bigint): PollWorldLike;
}

/** A turn the engine wants custody consent for, described in human terms. */
export interface ConsentRequest {
  /** A faithful, human reading of exactly what the turn does. */
  explanation: string;
  /** A stable id for the turn (bound in the confirm-intent chrome). */
  turnId: string;
  origin?: string;
}
export type ConsentFn = (req: ConsentRequest) => Promise<boolean>;

/** The public, content-addressed poll spec a resolve yields (netlayer stand-in). */
export interface PollSpec {
  kind: string;
  addr: string;
  numOptions: number;
  quorumM: number;
}
/** Resolve a canonical uri to a poll spec, or `null` (fail-closed). May be async. */
export type ResolveObjectFn = (uri: string) => PollSpec | null | Promise<PollSpec | null>;

export interface PollEngineDeps {
  PollWorld: PollWorldCtor;
  /** The netlayer resolve (content-addr → object). */
  resolveObject: ResolveObjectFn;
  /** Custody consent — opens `confirm-intent` chrome in the extension. */
  consent: ConsentFn;
}

// ── uri grammar (§1) ────────────────────────────────────────────────────────
// Canonical: dregg://poll/<addr>[?q]   Mirror: https://dregg.net/d/poll/<addr>[?q]
// The detector matches loosely (any token); the engine validates STRICTLY —
// a well-formed content-addr is `b3_<hex>`. A token that matches the detector
// but not this is fail-closed here (never rendered as verified).
const CANONICAL_RE = /^dregg:\/\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i;
const MIRROR_RE = /^https?:\/\/dregg\.net\/d\/([a-z0-9]+)\/([^?#\s]+)(?:[?#].*)?$/i;
const VALID_ADDR_RE = /^b3_[0-9a-f]{6,}$/i;

/** Parse either uri form to `{ kind, addr }`, or `null` if it is not a dregg-thing. */
export function parseDreggUri(uri: string): { kind: string; addr: string } | null {
  const s = uri.trim();
  const m = CANONICAL_RE.exec(s) || MIRROR_RE.exec(s);
  if (!m) return null;
  return { kind: m[1].toLowerCase(), addr: m[2] };
}

/** The canonical key for a dregg-thing (both uri forms map to the same key). */
export function canonicalUri(uri: string): string | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  return `dregg://${parsed.kind}/${parsed.addr}`;
}

/** A stable content-addressing stand-in: derive poll config from the addr bytes.
 *
 * The REAL netlayer (build order §4) fetches the content-addressed object and
 * checks `addr == blake3(object)`. Until that lands, we derive a deterministic
 * `(numOptions, quorumM)` from the addr so a well-formed `b3_<hex>` upgrades to
 * a stable poll, and a malformed token fails closed. This is honest about the
 * gap: verification of the *tally* is real (in-wasm light-client recompute);
 * the addr↔object binding is the deferred netlayer tooth. */
export function defaultResolveObject(uri: string): PollSpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "poll") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  // FNV-1a over the hex tail → a stable, addr-pinned poll shape.
  let h = 0x811c9dc5;
  const tail = parsed.addr.slice(3);
  for (let i = 0; i < tail.length; i++) {
    h ^= tail.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  const numOptions = 2 + (h % 4); // 2..=5
  const quorumM = 1 + ((h >>> 8) % 3); // 1..=3
  return { kind: "poll", addr: parsed.addr, numOptions, quorumM };
}

/** The viewer's own ballot index — one ballot per resolved poll, so a second
 * click is a genuine double-vote the nullifier refuses (not a fresh voter). */
const VIEWER_VOTER = 0;

/**
 * THE ENGINE. Owns one `PollWorld` per resolved uri; every response is tiered.
 * Runs only in the extension (background) context. Never returns secret state.
 */
export class PollEngine {
  private worlds = new Map<string, PollWorldLike>();
  private specs = new Map<string, PollSpec>();

  constructor(private deps: PollEngineDeps) {}

  async handle(req: PollPortRequest, origin?: string): Promise<PollPortResponse> {
    try {
      switch (req.op) {
        case "resolve":
          return await this.resolve(req.uri);
        case "render":
          return this.render(req.uri);
        case "verify":
          return this.verify(req.uri);
        case "fire":
          return await this.fire(req.uri, req.turn, req.arg, origin);
        default:
          return { ok: false, tier: "none", error: "unknown op" } as ResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) };
    }
  }

  private async world(uri: string): Promise<PollWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveObject(key);
    if (!spec) return null;
    const w = new this.deps.PollWorld(spec.numOptions, BigInt(spec.quorumM));
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  private async resolve(uri: string): Promise<ResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve object" };
    const spec = this.specs.get(key)!;
    // The in-wasm self-verify: executor tally == light-client recompute.
    const verified = w.verified();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr, optionCount: w.optionCount(), quorum: spec.quorumM },
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): RenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    // Never render an unverified board as if verified (§6 fail-closed).
    if (!w.verified()) return { ok: false, tier: "none", error: "unverified" };
    return { ok: true, tier: "extension", html: w.renderHtml(), optionCount: w.optionCount() };
  }

  private verify(uri: string): VerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.verified();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      receiptCount: w.receiptCount(),
      total: Number(w.total()),
    };
  }

  private async fire(uri: string, turn: string, arg: number, origin?: string): Promise<FireResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (turn !== "cast") return { ok: false, tier: "none", error: `unknown turn: ${turn}` };
    const spec = this.specs.get(key)!;
    if (!Number.isInteger(arg) || arg < 0 || arg >= w.optionCount()) {
      return { ok: false, tier: "none", error: "option out of range" };
    }

    // Custody consent (§3, §4.5) — the un-overlayable confirm-intent chrome.
    // Every cast is a real turn, so every cast asks. Consent BEFORE any commit.
    const approved = await this.deps.consent({
      explanation:
        `Cast your ballot for option ${arg} in poll ${spec.addr}. ` +
        `This commits one verified vote (one ballot, one vote) to the tally.`,
      turnId: `${key}#cast:${arg}`,
      origin,
    });
    if (!approved) {
      return { ok: true, tier: "extension", refused: true, reason: "consent denied", verified: w.verified(), total: Number(w.total()) };
    }

    // The real cap-gated verified turn: this viewer's own ballot. A second cast
    // is refused by the nullifier / WriteOnce(VOTE) — surfaced, not swallowed.
    try {
      w.castAs(VIEWER_VOTER, arg);
    } catch (e) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: String((e as Error)?.message ?? e),
        verified: w.verified(),
        receiptCount: w.receiptCount(),
        total: Number(w.total()),
      };
    }
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified: w.verified(),
      receiptCount: w.receiptCount(),
      total: Number(w.total()),
    };
  }
}
