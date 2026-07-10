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

// ═══════════════════════════════════════════════════════════════════════════
// THE COMPOSITION PORT — `<dregg-embed>` (a whole child CELL) and
// `<dregg-transclude>` (a value QUOTE). DOC-CELL-COMPOSITION.md §1/§2.3,
// DREGG-DOCUMENT-FOUNDATION.md §1.1–1.5, DREGG-WEB-SPEC.md pillar 5.
//
// The SAME split as the poll port: the ENGINE (background, wasm-side) resolves +
// verifies + renders + makes the trust/cap decision; the element is a thin,
// closed-shadow VIEW. No wasm, no keys, no cap-lattice ever reaches the page —
// only these tiered responses. The two operators are DISTINCT (§1):
//
//   resolveCell  — `<dregg-embed>`  — a whole child cell. LIVE by default
//                  (re-resolves to the child's tip) OR pinned to a receipt. Its
//                  own membrane boundary → its own shadow root. This is Op::Embed.
//   resolveValue — `<dregg-transclude>` — a VALUE quote: a snapshot of a
//                  finalized receipt. Never rots, never updates, UNEDITABLE.
//                  (The Xanadu quote.) Fail-CLOSED if it cannot be verified.
// ═══════════════════════════════════════════════════════════════════════════

/** The five resolution states of an embedded child cell (§2.3). The renderer
 * NEVER forges and NEVER panics — each is a first-class *state* of the output. */
export type CellResolution = "rendered" | "darkened" | "unresolved" | "cycle" | "unbound";

/** `Pin::Live` re-resolves to the child's tip every render; `Pin::At(receipt)`
 * freezes an immutable child receipt — a citation that never rots (§2.2). */
export type Pin = { kind: "live" } | { kind: "at"; receipt: string };

/** The public provenance/citation an embed or a quote carries. ALWAYS survives —
 * even a darkened embed keeps its citation (the membrane withholds only bytes). */
export interface Provenance {
  /** which cell (canonical `dregg://` uri). */
  cell: string;
  /** who owns/authored it (public), if known. */
  author?: string;
  /** the cited/pinned receipt (a pinned embed or a value quote). */
  receipt?: string;
  /** how it resolved: live tip vs a frozen receipt. */
  pin?: "live" | "at";
}

// ── the composition request/response protocol ───────────────────────────────
export type CellPortRequest =
  | { op: "resolveCell"; uri: string; pin?: Pin; ancestors?: string[] }
  | { op: "resolveValue"; uri: string };

export interface ResolveCellResponse {
  ok: boolean;
  /** which of the five states this child resolved to. */
  state: CellResolution;
  tier: TrustTier;
  /** the child's rendered HTML — PRESENT ONLY when `state === "rendered"`.
   *  It may itself contain nested `<dregg-*>` tags → the fold is RECURSIVE.
   *  On `darkened` the engine WITHHOLDS the bytes: this is `undefined` (the
   *  membrane projection — provenance survives, bytes never leave the engine). */
  html?: string;
  /** the citation/provenance — present for every non-error state, darkened too. */
  provenance?: Provenance;
  /** the canonical uri (for the light-DOM fallback link on a failed resolve). */
  canonical?: string;
  /** a human reason for a non-rendered state (unresolved/cycle/unbound). */
  reason?: string;
  error?: string;
}

export interface ResolveValueResponse {
  ok: boolean;
  /** the anchored quote verifier's verdict. `false` ⇒ the element fails closed. */
  verified: boolean;
  tier: TrustTier;
  /** the quoted, engine-rendered bytes — PRESENT ONLY when `verified`. */
  bytes?: string;
  provenance?: Provenance;
  error?: string;
}

export type CellPortResponse = ResolveCellResponse | ResolveValueResponse;

/** The transport a composition element holds — a channel to the CellEngine. */
export interface CellPort {
  request(req: CellPortRequest): Promise<CellPortResponse>;
}

// ── the resolver seam (the netlayer + membrane stand-in) ────────────────────
/** A child cell the netlayer fetched + the membrane projected for this viewer. */
export interface ResolvedCell {
  /** the child's rendered HTML (may embed grandchildren as nested `<dregg-*>`). */
  html: string;
  provenance: Provenance;
  /** the viewer's caps reach it. `false` ⇒ the ENGINE darkens (withholds html). */
  inCap: boolean;
}
/** A whole-cell lookup: found (with the projected cell) or not (why). */
export type CellLookup =
  | { found: true; cell: ResolvedCell }
  | { found: false; reason: "unbound" | "unresolved" };
/** Resolve a canonical cell uri (honoring the pin) to a lookup. May be async. */
export type ResolveCellFn = (uri: string, pin: Pin) => CellLookup | Promise<CellLookup>;

/** A finalized value quote: the bytes a source cell committed at a cited receipt. */
export interface ValueQuote {
  bytes: string;
  provenance: Provenance;
  /** the anchored verifier's verdict over the cited receipt. */
  verified: boolean;
}
/** Resolve a value uri to a quote, or `null` (unresolvable → fail-closed). */
export type ResolveValueFn = (uri: string) => ValueQuote | null | Promise<ValueQuote | null>;

export interface CellEngineDeps {
  resolveCell: ResolveCellFn;
  resolveValue: ResolveValueFn;
}

/**
 * THE COMPOSITION ENGINE. Runs only in the extension (background) context. It
 * makes the CAP/TRUST decision (darkening is engine-side — the bytes never leave
 * here on an out-of-cap child) and the CYCLE decision (the element supplies its
 * DOM ancestor chain — the composition tree IS the DOM — and the engine checks
 * membership). Every response is tiered; it never returns secret state and never
 * forges a child it could not resolve.
 */
export class CellEngine {
  constructor(private deps: CellEngineDeps) {}

  async handle(req: CellPortRequest): Promise<CellPortResponse> {
    try {
      switch (req.op) {
        case "resolveCell":
          return await this.resolveCell(req.uri, req.pin ?? { kind: "live" }, req.ancestors ?? []);
        case "resolveValue":
          return await this.resolveValue(req.uri);
        default:
          return { ok: false, state: "unresolved", tier: "none", error: "unknown op" } as ResolveCellResponse;
      }
    } catch (e) {
      return { ok: false, state: "unresolved", tier: "none", error: String((e as Error)?.message ?? e) };
    }
  }

  /** `<dregg-embed>`: resolve a whole child cell to one of the five states. */
  private async resolveCell(uri: string, pin: Pin, ancestors: string[]): Promise<ResolveCellResponse> {
    const canonical = canonicalUri(uri);
    if (!canonical) {
      return { ok: false, state: "unresolved", tier: "none", canonical: uri, reason: "not a dregg-thing" };
    }
    // CYCLE (§7): the target already sits above us in the composition tree.
    // A cycle is a first-class STATE, never a hang / stack overflow.
    if (ancestors.includes(canonical)) {
      return {
        ok: true,
        state: "cycle",
        tier: "extension",
        canonical,
        provenance: { cell: canonical, pin: pin.kind === "at" ? "at" : "live" },
        reason: "embedding this cell here would loop",
      };
    }
    const lookup = await this.deps.resolveCell(canonical, pin);
    if (!lookup.found) {
      // UNBOUND: a Name that binds to nothing (heals on rebind).
      // UNRESOLVED: a cell that could not be fetched at all (surfaced, not swallowed).
      return {
        ok: true,
        state: lookup.reason,
        tier: "extension",
        canonical,
        provenance: { cell: canonical },
        reason: lookup.reason === "unbound" ? "the name binds to nothing" : "the child could not be fetched",
      };
    }
    const cell = lookup.cell;
    const prov: Provenance = { ...cell.provenance, pin: pin.kind === "at" ? "at" : "live" };
    if (!cell.inCap) {
      // DARKENED — the membrane projection. Provenance survives; the bytes are
      // WITHHELD (html is undefined — they never leave the engine). §2.2.2.
      return { ok: true, state: "darkened", tier: "extension", canonical, provenance: prov, reason: "out of cap" };
    }
    // RENDERED — the child (its html may nest more `<dregg-*>` → the recursion).
    return { ok: true, state: "rendered", tier: "extension", canonical, html: cell.html, provenance: prov };
  }

  /** `<dregg-transclude>`: resolve a VALUE quote. Fail-CLOSED if unverifiable. */
  private async resolveValue(uri: string): Promise<ResolveValueResponse> {
    const canonical = canonicalUri(uri) ?? uri.trim();
    const quote = await this.deps.resolveValue(canonical);
    if (!quote) {
      return { ok: false, verified: false, tier: "none", error: "quote could not be resolved" };
    }
    if (!quote.verified) {
      // The anchored verifier refused — a bad quote is NEVER shown as a value.
      return { ok: false, verified: false, tier: "none", provenance: quote.provenance, error: "quote failed to verify" };
    }
    return { ok: true, verified: true, tier: "extension", bytes: quote.bytes, provenance: quote.provenance };
  }
}

/**
 * A dependency-free, in-memory web-of-cells (the netlayer + nameservice + value
 * store stand-in). The REAL substrate resolver (`WebOfCells::fetch` +
 * `Membrane::project` + the anchored `verify_anchored`) is named wiring; this is
 * the standalone analogue the fixture drives, exactly as `defaultResolveObject`
 * is for polls. A cell absent from the map is `unresolved`; a name explicitly
 * bound to nothing is `unbound`; `inCap: false` darkens; a value quote whose
 * `verified` is false fails closed.
 */
export class MapWebOfCells {
  private cells = new Map<string, ResolvedCell>();
  private unbound = new Set<string>();
  private values = new Map<string, ValueQuote>();

  setCell(uri: string, cell: ResolvedCell): this {
    const key = canonicalUri(uri) ?? uri;
    this.cells.set(key, cell);
    this.unbound.delete(key);
    return this;
  }
  /** Mark a name as currently bound to nothing (→ `unbound`; a later `setCell` heals it). */
  setUnbound(uri: string): this {
    const key = canonicalUri(uri) ?? uri;
    this.unbound.add(key);
    this.cells.delete(key);
    return this;
  }
  setValue(uri: string, quote: ValueQuote): this {
    this.values.set(canonicalUri(uri) ?? uri, quote);
    return this;
  }

  resolveCell: ResolveCellFn = (uri) => {
    const key = canonicalUri(uri) ?? uri;
    const cell = this.cells.get(key);
    if (cell) return { found: true, cell };
    if (this.unbound.has(key)) return { found: false, reason: "unbound" };
    return { found: false, reason: "unresolved" };
  };

  resolveValue: ResolveValueFn = (uri) => {
    return this.values.get(canonicalUri(uri) ?? uri) ?? null;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// THE DOCUMENT-AUTHORING PORT — `<dregg-doc>` (a verifiable document surface).
// DREGG-DOCUMENT-FOUNDATION.md (conflicts-as-objects), wasm/src/bindings_doc.rs
// (`DocCollabWorld`). This is the culminating authoring path: a person authors a
// verifiable document a STRANGER can check — fork → diverge → stitch → a
// first-class CONFLICT (both live alternatives, side by side, attributed) →
// resolve (pick an alternative) → PUBLISH as a real cap-gated verified turn whose
// receipt commits the resealed umem `heap_root` (limb 28).
//
// The SAME split as the poll/composition ports: the ENGINE (background, wasm-side)
// owns the `DocCollabWorld`, the resolve, the render, the resolution, and the
// verified-turn publish — and routes the publish through the un-overlayable
// confirm-intent consent. The element is a thin, closed-shadow VIEW: no wasm, no
// keys, no doc graph ever reaches the page — only these tiered responses. A
// CONFLICT is NEVER silently resolved or hidden here: the engine renders BOTH
// alternatives (its `viewHtml` ConflictView) and only a consented publish
// collapses it.
// ═══════════════════════════════════════════════════════════════════════════

/** The `DocCollabWorld` wasm surface this engine needs (a structural subset of
 *  `wasm/src/bindings_doc.rs`'s `#[wasm_bindgen]` methods). */
export interface DocWorldLike {
  /** The doc-cell's id (hex) — the document's sovereignty boundary. */
  cellId(): string;
  /** The document's commitment: the committed umem-heap boundary `heap_root` (hex). */
  commitmentHex(): string;
  /** The audit-tape length (one receipt per published boundary, incl. genesis). */
  receiptCount(): number;
  /** True iff a stitched merge is currently carrying an unresolved conflict. */
  hasConflict(): boolean;
  /** The light-client invariant: committed `heap_root == substrate_commit(published)`. */
  boundaryMatchesProjection(): boolean;
  /** The pending conflict's alternatives as JSON: `[{author, text}]`. */
  alternativesJson(): string;
  /** The current published document's rendered text (the resolved reading). */
  publishedText(): string;
  /** The document view-tree JSON (`{kind, props, children}`). */
  viewTreeJson(): string;
  /** The rendered HTML fragment (the ConflictView when a conflict is held). */
  viewHtml(): string;
  /** The affordance wire: `stitch` (diverge+merge) | `resolve` (collapse+publish). */
  fire(turn: string, arg: number): void;
}
export interface DocWorldCtor {
  new (): DocWorldLike;
}

/** One live alternative in a conflict — attributed, NEVER hidden. */
export interface DocAlternative {
  author: string;
  text: string;
}

// ── the document request/response protocol ──────────────────────────────────
export type DocPortRequest =
  | { op: "resolveDoc"; uri: string }
  | { op: "renderDoc"; uri: string }
  | { op: "stitch"; uri: string }
  | { op: "resolveConflict"; uri: string; choice: number }
  | { op: "publish"; uri: string }
  | { op: "verify"; uri: string };

export interface DocResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  /** The document's public shape (never the graph itself). */
  object?: { kind: string; addr: string; cellId: string };
  /** True when the document currently carries a first-class conflict. */
  hasConflict?: boolean;
  /** Both live alternatives (attributed) — present whenever a conflict is held. */
  alternatives?: DocAlternative[];
  /** The committed umem boundary `heap_root` (hex). */
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export interface DocRenderResponse {
  ok: boolean;
  tier: TrustTier;
  /** The engine's `viewHtml()` — the ConflictView (both alternatives side by side,
   *  attributed, + a resolution button per choice) OR the clean published doc. */
  html?: string;
  hasConflict?: boolean;
  alternatives?: DocAlternative[];
  error?: string;
}

export interface DocConflictResponse {
  ok: boolean;
  tier: TrustTier;
  /** True once an alternative is STAGED (picked). The conflict is STILL shown —
   *  it collapses only on a consented publish, so nothing is hidden by picking. */
  staged?: boolean;
  choice?: number;
  hasConflict?: boolean;
  error?: string;
}

export interface DocPublishResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the publish turn was refused (consent denied / bad choice). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  hasConflict?: boolean;
  receiptCount?: number;
  /** The NEW committed umem boundary `heap_root` (hex) after the publish turn. */
  commitment?: string;
  /** The light-client witness: the committed `heap_root` EQUALS the independent
   *  recompute of `substrate_commit(published)` — a stranger can re-check it. */
  substrateMatches?: boolean;
  error?: string;
}

export interface DocVerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export type DocPortResponse =
  | DocResolveResponse
  | DocRenderResponse
  | DocConflictResponse
  | DocPublishResponse
  | DocVerifyResponse;

/** The transport the `<dregg-doc>` element holds — a channel to the DocEngine. */
export interface DocPort {
  request(req: DocPortRequest): Promise<DocPortResponse>;
}

/** The public document spec a resolve yields (netlayer stand-in). `stitch` asks
 *  the engine to surface the demo divergence so the loaded document ALREADY
 *  carries a first-class conflict (the authoring case the fixture exercises). */
export interface DocSpec {
  kind: string;
  addr: string;
  stitch?: boolean;
}
/** Resolve a canonical doc uri to a spec, or `null` (fail-closed). May be async. */
export type ResolveDocFn = (uri: string) => DocSpec | null | Promise<DocSpec | null>;

export interface DocEngineDeps {
  DocWorld: DocWorldCtor;
  /** The netlayer resolve (content-addr → document spec). */
  resolveDoc: ResolveDocFn;
  /** Custody consent — opens `confirm-intent` chrome in the extension for a publish. */
  consent: ConsentFn;
}

/** The default (test/stand-in) doc resolver: validate the `dregg://doc/<addr>`
 *  content-address and yield a fresh document. The REAL netlayer fetches the
 *  content-addressed document and checks `addr == blake3(document)`; this is the
 *  standalone analogue (exactly as `defaultResolveObject` is for polls). A fresh
 *  document carries no conflict — the authoring divergence is surfaced explicitly
 *  (`stitch`); a malformed addr fails closed. */
export function defaultResolveDoc(uri: string): DocSpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "doc") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  return { kind: "doc", addr: parsed.addr, stitch: false };
}

/**
 * THE DOCUMENT ENGINE. Owns one `DocCollabWorld` per resolved uri; every response
 * is tiered. Runs only in the extension (background) context. It renders the
 * document (a ConflictView holds BOTH alternatives — never hidden), stages a
 * resolution pick, and PUBLISHES (a real cap-gated verified turn — reseal the
 * umem `heap_root`, commit `SetField(20)+IncrementNonce`) ONLY after the injected
 * consent approves the faithful reading. Never returns the doc graph itself.
 */
export class DocEngine {
  private worlds = new Map<string, DocWorldLike>();
  private specs = new Map<string, DocSpec>();
  /** The staged resolution pick per doc — set by `resolveConflict`, consumed by
   *  `publish`. Staging does NOT collapse the conflict; the publish does. */
  private staged = new Map<string, number>();

  constructor(private deps: DocEngineDeps) {}

  async handle(req: DocPortRequest, origin?: string): Promise<DocPortResponse> {
    try {
      switch (req.op) {
        case "resolveDoc":
          return await this.resolve(req.uri);
        case "renderDoc":
          return this.render(req.uri);
        case "stitch":
          return await this.stitch(req.uri);
        case "resolveConflict":
          return this.resolveConflict(req.uri, req.choice);
        case "publish":
          return await this.publish(req.uri, origin);
        case "verify":
          return this.verify(req.uri);
        default:
          return { ok: false, tier: "none", verified: false, error: "unknown op" } as DocResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) };
    }
  }

  private async world(uri: string): Promise<DocWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveDoc(key);
    if (!spec) return null;
    const w = new this.deps.DocWorld();
    // Surface the authoring divergence so the loaded document carries a first-class
    // conflict (the case the authoring path is FOR). A fresh document has none.
    if (spec.stitch) w.fire("stitch", 0);
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  /** Parse the wasm's `[{author, text}]` alternatives — both alternatives always
   *  travel together (the anti-forge tooth binds them into `substrate_commit`). */
  private alternatives(w: DocWorldLike): DocAlternative[] {
    try {
      const rows = JSON.parse(w.alternativesJson());
      if (!Array.isArray(rows)) return [];
      return rows.map((r) => ({ author: String(r.author ?? ""), text: String(r.text ?? "") }));
    } catch {
      return [];
    }
  }

  private async resolve(uri: string): Promise<DocResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve document" };
    const spec = this.specs.get(key)!;
    // The light-client invariant: the committed boundary equals the canonical
    // projection of the published reading (the membership/anti-forge guarantee).
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr, cellId: w.cellId() },
      hasConflict: w.hasConflict(),
      alternatives: this.alternatives(w),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): DocRenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    // Never render a document whose boundary does not match its projection (§6).
    if (!w.boundaryMatchesProjection()) return { ok: false, tier: "none", error: "unverified" };
    return {
      ok: true,
      tier: "extension",
      html: w.viewHtml(),
      hasConflict: w.hasConflict(),
      alternatives: this.alternatives(w),
    };
  }

  /** STITCH — surface a concurrent divergence (the pushout) as a first-class
   *  conflict, held off-heap (the committed boundary does not move). */
  private async stitch(uri: string): Promise<DocConflictResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    try {
      w.fire("stitch", 0);
    } catch (e) {
      return { ok: false, tier: "none", error: String((e as Error)?.message ?? e) };
    }
    return { ok: true, tier: "extension", hasConflict: w.hasConflict() };
  }

  /** RESOLVE-CONFLICT — STAGE the pick of an alternative. The conflict is STILL
   *  shown (both alternatives) until a consented publish collapses it; picking
   *  never hides an alternative. */
  private resolveConflict(uri: string, choice: number): DocConflictResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (!w.hasConflict()) return { ok: false, tier: "none", error: "no conflict to resolve" };
    if (!Number.isInteger(choice) || choice < 0) return { ok: false, tier: "none", error: "invalid choice" };
    this.staged.set(key, choice);
    return { ok: true, tier: "extension", staged: true, choice, hasConflict: w.hasConflict() };
  }

  /** PUBLISH — the real cap-gated verified turn. Consent BEFORE any commit (the
   *  faithful reading of the publish turn, in un-overlayable chrome). On approval,
   *  `fire("resolve", choice)` collapses the conflict, reseals the umem `heap_root`
   *  to `substrate_commit(resolved)`, and commits `SetField(20)+IncrementNonce`;
   *  the receipt witnesses the new boundary at limb 28. */
  private async publish(uri: string, origin?: string): Promise<DocPublishResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    if (!w.hasConflict()) return { ok: false, tier: "none", error: "nothing to publish (no held conflict)" };
    if (!this.staged.has(key)) return { ok: false, tier: "none", error: "pick an alternative first" };
    const choice = this.staged.get(key)!;
    const spec = this.specs.get(key)!;
    const chosen = this.alternatives(w)[choice]?.author ?? `choice ${choice}`;

    // Custody consent (the load-bearing property): the faithful reading the page
    // cannot overlay or clickjack. Every publish is a real turn, so every publish asks.
    const approved = await this.deps.consent({
      explanation:
        `Publish the resolved document ${spec.addr} to the umem-heap. ` +
        `You are keeping the alternative by ${chosen} and committing ONE verified turn ` +
        `that binds the new document commitment (heap_root) into the receipt (limb 28).`,
      turnId: `${key}#publish:${choice}`,
      origin,
    });
    if (!approved) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: "consent denied",
        verified: w.boundaryMatchesProjection(),
        hasConflict: w.hasConflict(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
      };
    }

    // The real verified turn: resolve + publish (reseal heap_root, commit turn).
    try {
      w.fire("resolve", choice);
    } catch (e) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: String((e as Error)?.message ?? e),
        verified: w.boundaryMatchesProjection(),
        hasConflict: w.hasConflict(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
      };
    }
    this.staged.delete(key);
    const substrateMatches = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified: substrateMatches,
      hasConflict: w.hasConflict(),
      receiptCount: w.receiptCount(),
      commitment: w.commitmentHex(),
      substrateMatches,
    };
  }

  /** VERIFY — the LIGHT-CLIENT check a stranger runs: independently recompute
   *  `substrate_commit(published)` and confirm it equals the committed `heap_root`
   *  the receipt bound. This is the "a stranger checks the receipt chain" property. */
  private verify(uri: string): DocVerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE FREE-TEXT AUTHORING PORT — `<dregg-doc editable>` (a person types PROSE).
// DREGG-DOCUMENT-FOUNDATION.md, wasm/src/bindings_doc.rs (`DocTextWorld`). This
// closes the goal's "a person authors a verifiable document a STRANGER can check"
// for FREE TEXT — not only picking a conflict alternative. A keystroke becomes a
// real `dregg_doc::Patch` (via `Doc::edit`'s token-LCS diff → the MINIMAL
// Add/Delete patch — kept words reuse their atom ids; NOT a rewrite), and a
// publish reseals the doc-cell's umem boundary as a real cap-gated verified turn.
//
// The SAME split as every other port: the ENGINE (background, wasm-side) owns the
// `DocTextWorld`, the diff→patch, the render, and the verified-turn publish — and
// routes the publish through the un-overlayable confirm-intent consent BEFORE any
// commit. The element is a thin, closed-shadow VIEW over a contenteditable: no
// wasm, no keys, no doc graph reach the page — only these tiered responses.
//
// The load-bearing difference from `DocEngine`: an unpublished edit legitimately
// leaves the WORKING document ahead of the last published boundary. That is a
// first-class `dirty` state (surfaced, never hidden) — NOT an unverified one:
// `boundaryMatchesProjection()` still holds (it binds the last *published* doc,
// which only advances on `publishEdit`). So editing never fails the render closed;
// only an unresolvable/unverifiable doc-cell does.
// ═══════════════════════════════════════════════════════════════════════════

/** The `DocTextWorld` wasm surface this engine needs (a structural subset of
 *  `wasm/src/bindings_doc.rs`'s `#[wasm_bindgen]` methods). */
export interface DocTextWorldLike {
  /** The doc-cell's id (hex). */
  cellId(): string;
  /** The committed umem-heap boundary `heap_root` (hex). */
  commitmentHex(): string;
  /** The audit-tape length (one receipt per published boundary, incl. genesis seed). */
  receiptCount(): number;
  /** The invariant a stranger re-checks: committed `heap_root == substrate_commit(published)`. */
  boundaryMatchesProjection(): boolean;
  /** The current WORKING document's rendered text (post-edit, pre-publish). */
  currentText(): string;
  /** The rendered HTML fragment (the free-text reading through the web renderer). */
  render(): string;
  /** Diff `newText` into the doc (token-LCS → the minimal patch) + commit it to the
   *  history. Returns a JSON summary `{ atoms_added, atoms_tombstoned, text }` — the
   *  counts prove minimality (a word replaced ⇒ 1 add + 1 tombstone, NOT a rewrite). */
  applyTextEdit(newText: string): string;
  /** Reseal `heap_root = substrate_commit(working)` + commit a real cap-gated verified
   *  turn. Returns a JSON receipt `{ receiptCount, commitmentHex }`. Throws (fail-closed)
   *  if the publish turn is rejected. */
  publishEdit(): string;
}
export interface DocTextWorldCtor {
  // `initialText` seeds the document; `authorId` (a wasm `u32`) stamps inserted atoms.
  new (initialText: string, authorId: number): DocTextWorldLike;
}

// ── the free-text request/response protocol ─────────────────────────────────
export type DocTextPortRequest =
  | { op: "resolveText"; uri: string }
  | { op: "renderText"; uri: string }
  | { op: "applyEdit"; uri: string; text: string }
  | { op: "publishText"; uri: string }
  | { op: "verifyText"; uri: string };

export interface DocTextResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  object?: { kind: string; addr: string; cellId: string };
  /** The current working text (the seed at resolve time). */
  text?: string;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export interface DocTextRenderResponse {
  ok: boolean;
  tier: TrustTier;
  /** The engine's `render()` HTML (the rendered reading). */
  html?: string;
  /** The plain working text the contenteditable region edits. */
  text?: string;
  /** True when there are edits not yet published (the working doc leads the boundary). */
  dirty?: boolean;
  error?: string;
}

export interface DocTextEditResponse {
  ok: boolean;
  tier: TrustTier;
  /** Fresh atoms the edit inserted (new ids). */
  atomsAdded?: number;
  /** Previously-alive atoms the edit tombstoned. Together with `atomsAdded` these
   *  prove the patch is MINIMAL (a replaced word ⇒ 1 + 1), never a full rewrite. */
  atomsTombstoned?: number;
  /** The document's canonical text after the edit (what the reconciler repaints). */
  text?: string;
  dirty?: boolean;
  error?: string;
}

export interface DocTextPublishResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the publish turn was refused (consent denied / rejected turn). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  receiptCount?: number;
  /** The NEW committed umem boundary `heap_root` (hex) after the publish turn. */
  commitment?: string;
  /** The light-client witness: committed `heap_root` == recompute of
   *  `substrate_commit(published)` — a stranger can re-check it. */
  substrateMatches?: boolean;
  dirty?: boolean;
  error?: string;
}

export interface DocTextVerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export type DocTextPortResponse =
  | DocTextResolveResponse
  | DocTextRenderResponse
  | DocTextEditResponse
  | DocTextPublishResponse
  | DocTextVerifyResponse;

/** The transport `<dregg-doc editable>` holds — a channel to the DocTextEngine. */
export interface DocTextPort {
  request(req: DocTextPortRequest): Promise<DocTextPortResponse>;
}

/** The public free-text document spec a resolve yields (netlayer stand-in): the
 *  seed prose + the editing author. The REAL netlayer fetches the content-addressed
 *  document and checks `addr == blake3(document)`; this is the standalone analogue
 *  (exactly as `defaultResolveObject`/`defaultResolveDoc` are). */
export interface DocTextSpec {
  kind: string;
  addr: string;
  /** The seed prose the doc-cell is minted with. */
  initialText: string;
  /** The editing author id (stamped onto inserted atoms). */
  authorId: number;
}
/** Resolve a canonical `dregg://doctext/<addr>` uri to a spec, or `null` (fail-closed). */
export type ResolveDocTextFn = (uri: string) => DocTextSpec | null | Promise<DocTextSpec | null>;

/** The default (test/stand-in) free-text resolver: validate the `dregg://doctext/<addr>`
 *  content-address and yield a fresh, seeded document. A malformed addr fails closed. */
export function defaultResolveDocText(uri: string): DocTextSpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "doctext") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  return { kind: "doctext", addr: parsed.addr, initialText: "the quick brown fox", authorId: 1 };
}

export interface DocTextEngineDeps {
  DocTextWorld: DocTextWorldCtor;
  /** The netlayer resolve (content-addr → seeded free-text document). */
  resolveDocText: ResolveDocTextFn;
  /** Custody consent — opens `confirm-intent` chrome in the extension for a publish. */
  consent: ConsentFn;
}

/**
 * THE FREE-TEXT DOCUMENT ENGINE. Owns one `DocTextWorld` per resolved uri; every
 * response is tiered. Runs only in the extension (background) context. It diffs a
 * keystroke into the minimal patch (`applyEdit`), renders the working reading, and
 * PUBLISHES (a real cap-gated verified turn resealing the umem `heap_root`) ONLY
 * after the injected consent approves the faithful reading. It tracks a `dirty`
 * flag per doc — edits not yet published — surfaced (never hidden). Never returns
 * the doc graph itself.
 */
export class DocTextEngine {
  private worlds = new Map<string, DocTextWorldLike>();
  private specs = new Map<string, DocTextSpec>();
  /** Docs with edits applied but not yet published (working doc leads the boundary). */
  private dirty = new Set<string>();

  constructor(private deps: DocTextEngineDeps) {}

  async handle(req: DocTextPortRequest, origin?: string): Promise<DocTextPortResponse> {
    try {
      switch (req.op) {
        case "resolveText":
          return await this.resolve(req.uri);
        case "renderText":
          return this.render(req.uri);
        case "applyEdit":
          return await this.applyEdit(req.uri, req.text);
        case "publishText":
          return await this.publish(req.uri, origin);
        case "verifyText":
          return this.verify(req.uri);
        default:
          return { ok: false, tier: "none", verified: false, error: "unknown op" } as DocTextResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) };
    }
  }

  private async world(uri: string): Promise<DocTextWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveDocText(key);
    if (!spec) return null;
    // Minting the doc-cell publishes the seed to the umem-heap as a real verified
    // turn (the genesis boundary) — see `DocTextWorld::new`.
    const w = new this.deps.DocTextWorld(spec.initialText, spec.authorId);
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  private async resolve(uri: string): Promise<DocTextResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve document" };
    const spec = this.specs.get(key)!;
    // The light-client invariant over the last PUBLISHED boundary (the seed is
    // published at mint, so this holds at load — fail-closed otherwise).
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr, cellId: w.cellId() },
      text: w.currentText(),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): DocTextRenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    // A doc-cell whose PUBLISHED boundary does not match its projection fails closed
    // (§6). An unpublished EDIT is NOT this case — the published boundary still holds.
    if (!w.boundaryMatchesProjection()) return { ok: false, tier: "none", error: "unverified" };
    return { ok: true, tier: "extension", html: w.render(), text: w.currentText(), dirty: this.dirty.has(key) };
  }

  /** APPLY-EDIT — diff the new text into the minimal patch and commit it to the
   *  history (the working doc advances; the published boundary does NOT until a
   *  consented publish). Marks the doc dirty. */
  private async applyEdit(uri: string, text: string): Promise<DocTextEditResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    let summary: { atoms_added?: number; atoms_tombstoned?: number; text?: string };
    try {
      summary = JSON.parse(w.applyTextEdit(text));
    } catch (e) {
      return { ok: false, tier: "none", error: String((e as Error)?.message ?? e) };
    }
    this.dirty.add(key);
    return {
      ok: true,
      tier: "extension",
      atomsAdded: Number(summary.atoms_added ?? 0),
      atomsTombstoned: Number(summary.atoms_tombstoned ?? 0),
      text: String(summary.text ?? w.currentText()),
      dirty: true,
    };
  }

  /** PUBLISH-TEXT — the real cap-gated verified turn. Consent BEFORE any commit (the
   *  faithful reading, in un-overlayable chrome). On approval, `publishEdit` reseals
   *  `heap_root = substrate_commit(working)` and commits `SetField(PUBLISH_SLOT) +
   *  IncrementNonce`; the receipt witnesses the new boundary. */
  private async publish(uri: string, origin?: string): Promise<DocTextPublishResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };
    const spec = this.specs.get(key)!;

    // Custody consent (the load-bearing property): the faithful reading the page
    // cannot overlay or clickjack. Every publish is a real turn, so every publish asks.
    const approved = await this.deps.consent({
      explanation:
        `Publish your free-text edits to document ${spec.addr} to the umem-heap. ` +
        `This commits ONE verified turn that reseals the document commitment (heap_root) ` +
        `into a new receipt a stranger can re-check.`,
      turnId: `${key}#publishText`,
      origin,
    });
    if (!approved) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: "consent denied",
        verified: w.boundaryMatchesProjection(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
        dirty: this.dirty.has(key),
      };
    }

    // The real verified turn: reseal the boundary + commit. Fail-closed on a rejected turn.
    let receipt: { receiptCount?: number; commitmentHex?: string };
    try {
      receipt = JSON.parse(w.publishEdit());
    } catch (e) {
      return {
        ok: true,
        tier: "extension",
        refused: true,
        reason: String((e as Error)?.message ?? e),
        verified: w.boundaryMatchesProjection(),
        commitment: w.commitmentHex(),
        receiptCount: w.receiptCount(),
        dirty: this.dirty.has(key),
      };
    }
    this.dirty.delete(key);
    const substrateMatches = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified: substrateMatches,
      receiptCount: Number(receipt.receiptCount ?? w.receiptCount()),
      commitment: String(receipt.commitmentHex ?? w.commitmentHex()),
      substrateMatches,
      dirty: false,
    };
  }

  /** VERIFY-TEXT — the LIGHT-CLIENT check a stranger runs: independently recompute
   *  `substrate_commit(published)` and confirm it equals the committed `heap_root`. */
  private verify(uri: string): DocTextVerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.boundaryMatchesProjection();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }
}

// ═══════════════════════════════════════════════════════════════════════════
// THE VERIFIABLE STORY ENGINE — `<dregg-story>` (a choose-your-own-adventure a
// stranger can replay). docs/MEGASPEC-worlds-ide-and-the-verified-web.md §4.
//
// The SAME split as `<dregg-doc>`: this ENGINE (background, wasm-side) owns the
// real wasm `StoryWorld`, resolves the story over the netlayer, renders the
// current passage's prose + its choices, and ADVANCES the story (a real cap-gated
// verified turn) ONLY after the injected custody consent approves the faithful
// reading of the choice-turn. A gated/unavailable/invalid choice FAILS CLOSED
// WITHOUT ever prompting; a denied consent commits nothing. READ (`renderStory`)
// and VERIFY (`verifyStory`) need NO custody — the free, trustless tier a bare
// browser gets. The element reaches this ONLY through the "dregg:story" message —
// no wasm, no keys, no story graph ever leave this context. Absent a node,
// `defaultResolveStory` is the stand-in; a malformed addr fails closed — mirrors
// the poll/doc engines' `default*` resolvers exactly.
// ═══════════════════════════════════════════════════════════════════════════

/** One choice at the current passage — its index, text, and whether it is
 *  currently available (a gated choice is SHOWN, attributed, but not takeable). */
export interface StoryChoice {
  index: number;
  text: string;
  available: boolean;
}

/** The `StoryWorld` wasm surface this engine needs (the storyworld contract the
 *  parallel wasm lane implements; the fixture drives an in-memory stand-in). Every
 *  choice is a real verified turn; `verify()` replays the whole receipt chain. */
export interface StoryWorldLike {
  /** The current passage's name. */
  currentPassage(): string;
  /** The narrative prose to render for the current passage. */
  passageProse(): string;
  /** The choices at the current passage: JSON `[{index, text, available}]`. */
  choicesJson(): string;
  /** Take a choice as a verified turn: JSON `{ok, passage, receiptCount, commitmentHex, error?}`.
   *  Fails closed (`ok:false`) on a gated/invalid choice — the boundary does not move. */
  advance(index: number): string;
  /** Replay the receipt chain from genesis (the stranger's check). */
  verify(): boolean;
  /** The committed story commitment (hex). */
  commitmentHex(): string;
  /** How many verified turns (choices) are in the receipt tape. */
  receiptCount(): number;
}
export interface StoryWorldCtor {
  /** Mint a world from the VERIFIED `.scene` source (the real wasm `StoryWorld::new`
   *  compiles it; a fail-closed ctor throws on an unparseable scene). The fixture's
   *  in-memory stand-in ignores the argument and drives its own embedded graph. */
  new (scene?: string): StoryWorldLike;
}

// ── the COLLECTIVE surface (the killer mode) ─────────────────────────────────
// The crowd votes each branch; the winner advances. A parallel wasm lane adds
// these four methods to the real `StoryWorld`; the collective fixture drives an
// in-memory stand-in implementing EXACTLY this, as the story/poll fixtures do. A
// world that does not carry these methods is not collective (the engine's
// collective ops fail closed on it — see `asCollective`).
export interface CollectiveStoryWorldLike extends StoryWorldLike {
  /** The branch poll at the current passage: JSON `{passage, round, options: [{choiceIndex, label}]}`. */
  openBranchPoll(): string;
  /** Record one vote (ONE per voter, fail-closed): JSON `{ok, tally: [{label, count}], error?}`.
   *  `voter` is the caster's stable id — the custody provider's public key. */
  castVote(voter: string, optionIndex: number): string;
  /** The live tally for the open branch: JSON `[{label, count}]`. */
  branchTally(): string;
  /** Resolve the branch → advance(winner) → new passage: JSON `{ok, winningChoice,
   *  winningLabel, tally, passage, receiptCount, commitmentHex, tie?, error?}`. */
  closeBranchPoll(): string;
}

/** Feature-probe a world for the collective surface (never break single-player). */
function asCollective(w: StoryWorldLike): CollectiveStoryWorldLike | null {
  const c = w as Partial<CollectiveStoryWorldLike>;
  return typeof c.openBranchPoll === "function" &&
    typeof c.castVote === "function" &&
    typeof c.branchTally === "function" &&
    typeof c.closeBranchPoll === "function"
    ? (w as CollectiveStoryWorldLike)
    : null;
}

/** One branch option with its live tally — what a vote button renders. */
export interface BranchOption {
  choiceIndex: number;
  label: string;
  count: number;
}
/** One tally row (label → running count). */
export interface BranchTallyRow {
  label: string;
  count: number;
}

// ── the story request/response protocol ─────────────────────────────────────
export type StoryPortRequest =
  | { op: "resolveStory"; uri: string }
  | { op: "renderStory"; uri: string }
  | { op: "chooseChoice"; uri: string; index: number }
  | { op: "verifyStory"; uri: string }
  // ── collective mode ──
  | { op: "openBranch"; uri: string }
  | { op: "castBranchVote"; uri: string; optionIndex: number }
  | { op: "branchTally"; uri: string }
  | { op: "closeBranch"; uri: string };

export interface StoryResolveResponse {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  object?: { kind: string; addr: string };
  /** Whether this provider can authorize a choice (CUSTODY). READ + VERIFY never
   *  need it; `false` ⇒ the story renders + verifies but is read-only. */
  custody?: boolean;
  passage?: string;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

export interface StoryRenderResponse {
  ok: boolean;
  tier: TrustTier;
  passage?: string;
  /** The narrative prose for the current passage. */
  prose?: string;
  /** The choices (each attributed with its availability) — a gated one is shown. */
  choices?: StoryChoice[];
  custody?: boolean;
  error?: string;
}

export interface StoryChooseResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the choice-turn was refused (consent denied / gated / no custody). */
  refused?: boolean;
  reason?: string;
  verified?: boolean;
  passage?: string;
  receiptCount?: number;
  /** The NEW story commitment (hex) after the advance turn. */
  commitment?: string;
  error?: string;
}

export interface StoryVerifyResponse {
  ok: boolean;
  tier: TrustTier;
  verified: boolean;
  passage?: string;
  commitment?: string;
  receiptCount?: number;
  error?: string;
}

// ── the collective response shapes ──────────────────────────────────────────

export interface StoryOpenBranchResponse {
  ok: boolean;
  tier: TrustTier;
  passage?: string;
  /** Which voting round this branch is (increments each close). */
  round?: number;
  /** The passage prose to render above the vote UI (the free READ tier). */
  prose?: string;
  /** Each branch option with its live tally — a vote button per option. */
  options?: BranchOption[];
  tally?: BranchTallyRow[];
  total?: number;
  /** Whether the viewer can CAST a vote / CLOSE (custody). READ + tally never need it. */
  custody?: boolean;
  verified?: boolean;
  /** True when the passage is an ending (no branch → the story is over). */
  ended?: boolean;
  error?: string;
}

export interface StoryBranchVoteResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the vote-turn was refused (no custody / consent denied / double-vote). */
  refused?: boolean;
  reason?: string;
  tally?: BranchTallyRow[];
  total?: number;
  /** The stable voter id the vote was recorded under (the custody public key, hex). */
  voter?: string;
  error?: string;
}

export interface StoryBranchTallyResponse {
  ok: boolean;
  tier: TrustTier;
  tally?: BranchTallyRow[];
  total?: number;
  error?: string;
}

export interface StoryCloseBranchResponse {
  ok: boolean;
  tier: TrustTier;
  /** True when the close-turn was refused (no custody / consent denied / no votes). */
  refused?: boolean;
  reason?: string;
  winningChoice?: number;
  winningLabel?: string;
  /** Shown HONESTLY when the top count was shared (resolved by lowest index). */
  tie?: boolean;
  tally?: BranchTallyRow[];
  passage?: string;
  receiptCount?: number;
  /** The NEW story commitment (hex) after the winner advanced. */
  commitment?: string;
  verified?: boolean;
  error?: string;
}

export type StoryPortResponse =
  | StoryResolveResponse
  | StoryRenderResponse
  | StoryChooseResponse
  | StoryVerifyResponse
  | StoryOpenBranchResponse
  | StoryBranchVoteResponse
  | StoryBranchTallyResponse
  | StoryCloseBranchResponse;

/** The transport the `<dregg-story>` element holds — a channel to the StoryEngine. */
export interface StoryPort {
  request(req: StoryPortRequest): Promise<StoryPortResponse>;
}

/** The public, content-addressed story spec a resolve yields (netlayer stand-in). */
export interface StorySpec {
  kind: string;
  addr: string;
  /** The VERIFIED `.scene` SOURCE (addr == blake3(scene)) the real netlayer fetched.
   *  Present on a netlayer resolve; the StoryEngine hands it to `new StoryWorld(scene)`.
   *  Absent on the stand-in resolver (the fixture's stand-in world carries its own
   *  scene) — then the wasm `StoryWorld` ctor's own default/embedded scene is used. */
  scene?: string;
}
/** Resolve a canonical story uri to a spec, or `null` (fail-closed). May be async. */
export type ResolveStoryFn = (uri: string) => StorySpec | null | Promise<StorySpec | null>;

/** The default (test/stand-in) story resolver: validate the `dregg://story/<addr>`
 *  content-address and yield the story. The REAL netlayer fetches the
 *  content-addressed story and checks `addr == blake3(story)`; this is the
 *  standalone analogue. A malformed addr fails closed. */
export function defaultResolveStory(uri: string): StorySpec | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  if (parsed.kind !== "story") return null;
  if (!VALID_ADDR_RE.test(parsed.addr)) return null; // fail-closed on a bad addr
  return { kind: "story", addr: parsed.addr };
}

export interface StoryEngineDeps {
  StoryWorld: StoryWorldCtor;
  /** The netlayer resolve (content-addr → story spec). */
  resolveStory: ResolveStoryFn;
  /** Custody consent — opens `confirm-intent` chrome for a choice-turn. Absent
   *  (`null`/omitted) ⇒ READ-ONLY: the story renders + verifies, but choosing is
   *  refused (the honest "connect your cipherclerk to play" degrade). */
  consent?: ConsentFn | null;
  /** The collective voter identity — the custody provider's ed25519 public key (hex),
   *  so a vote is recorded under a STABLE id (an extension-less passkey voter yields a
   *  stable id from its PRF-wrapped key too). Returns `null` when there is no custody:
   *  a collective vote then FAILS CLOSED (READ + tally stay free). */
  voterIdentity?: (() => Promise<string | null> | string | null) | null;
}

/**
 * THE STORY ENGINE. Owns one `StoryWorld` per resolved uri; every response is
 * tiered. Runs only in the extension (background) context. It renders the current
 * passage (prose + choices), and ADVANCES (a real cap-gated verified turn) ONLY
 * after the injected consent approves the faithful reading of the choice — a
 * gated/invalid choice fails closed WITHOUT prompting. Never returns the story graph.
 */
export class StoryEngine {
  private worlds = new Map<string, StoryWorldLike>();
  private specs = new Map<string, StorySpec>();

  constructor(private deps: StoryEngineDeps) {}

  /** CUSTODY is present iff a consent provider is wired (extension/passkey). */
  private get hasCustody(): boolean {
    return typeof this.deps.consent === "function";
  }

  async handle(req: StoryPortRequest, origin?: string): Promise<StoryPortResponse> {
    try {
      switch (req.op) {
        case "resolveStory":
          return await this.resolve(req.uri);
        case "renderStory":
          return this.render(req.uri);
        case "chooseChoice":
          return await this.choose(req.uri, req.index, origin);
        case "verifyStory":
          return this.verify(req.uri);
        case "openBranch":
          return await this.openBranch(req.uri);
        case "castBranchVote":
          return await this.castBranchVote(req.uri, req.optionIndex, origin);
        case "branchTally":
          return this.branchTallyOp(req.uri);
        case "closeBranch":
          return await this.closeBranch(req.uri, origin);
        default:
          return { ok: false, tier: "none", verified: false, error: "unknown op" } as StoryResolveResponse;
      }
    } catch (e) {
      return { ok: false, tier: "none", verified: false, error: String((e as Error)?.message ?? e) } as StoryResolveResponse;
    }
  }

  private async world(uri: string): Promise<StoryWorldLike | null> {
    const key = canonicalUri(uri);
    if (!key) return null;
    const existing = this.worlds.get(key);
    if (existing) return existing;
    const spec = await this.deps.resolveStory(key);
    if (!spec) return null;
    // Mint the world from the VERIFIED scene source the netlayer fetched (addr ==
    // blake3(scene)); a fail-closed wasm ctor throws on an unparseable scene, so a
    // hostile story that slipped a bad addr past resolve still mints NOTHING. The
    // stand-in resolver carries no scene (`undefined`) — the fixture's stand-in world
    // and the wasm ctor's own embedded scene both handle that.
    let w: StoryWorldLike;
    try {
      w = new this.deps.StoryWorld(spec.scene);
    } catch {
      return null; // an unparseable/hostile scene mints no world (fail-closed)
    }
    this.worlds.set(key, w);
    this.specs.set(key, spec);
    return w;
  }

  /** Parse the world's `[{index, text, available}]` choices. */
  private choices(w: StoryWorldLike): StoryChoice[] {
    try {
      const rows = JSON.parse(w.choicesJson());
      if (!Array.isArray(rows)) return [];
      return rows.map((r, i) => ({
        index: Number(r.index ?? i),
        text: String(r.text ?? ""),
        available: r.available !== false,
      }));
    } catch {
      return [];
    }
  }

  private async resolve(uri: string): Promise<StoryResolveResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, verified: false, tier: "none", error: "not a dregg-thing" };
    const w = await this.world(key);
    if (!w) return { ok: false, verified: false, tier: "none", error: "could not resolve story" };
    const spec = this.specs.get(key)!;
    // The stranger's invariant: the story's receipt chain replays from genesis.
    const verified = w.verify();
    return {
      ok: true,
      verified,
      tier: verified ? "extension" : "none",
      object: { kind: spec.kind, addr: spec.addr },
      custody: this.hasCustody,
      passage: w.currentPassage(),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }

  private render(uri: string): StoryRenderResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    // Never render a story whose receipt chain does not replay (fail-closed).
    if (!w.verify()) return { ok: false, tier: "none", error: "unverified" };
    return {
      ok: true,
      tier: "extension",
      passage: w.currentPassage(),
      prose: w.passageProse(),
      choices: this.choices(w),
      custody: this.hasCustody,
    };
  }

  /** CHOOSE — the real cap-gated verified turn. Consent BEFORE any commit (the
   *  faithful reading of the choice-turn, in un-overlayable chrome). A gated/invalid
   *  choice, and a provider with no custody, both FAIL CLOSED without advancing. */
  private async choose(uri: string, index: number, origin?: string): Promise<StoryChooseResponse> {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };

    const refuse = (reason: string): StoryChooseResponse => ({
      ok: true,
      tier: w.verify() ? "extension" : "none",
      refused: true,
      reason,
      verified: w.verify(),
      passage: w.currentPassage(),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    });

    // CUSTODY: a choice is a real verified turn; no custody ⇒ read-only.
    if (!this.hasCustody) return refuse("no custody — connect your cipherclerk to play");

    // FAIL-CLOSED on a gated/unavailable/invalid choice — BEFORE any consent prompt.
    const choice = this.choices(w).find((c) => c.index === index);
    if (!choice) return refuse("no such choice");
    if (!choice.available) return refuse("choice is gated/unavailable");

    // Custody consent (the load-bearing property): the faithful reading the page
    // cannot overlay or clickjack. Every choice is a real turn, so every choice asks.
    const spec = this.specs.get(key)!;
    const approved = await this.deps.consent!({
      explanation:
        `Advance the story ${spec.addr}: choose "${choice.text}" at passage "${w.currentPassage()}". ` +
        `This commits ONE verified turn that binds the new story commitment into the receipt a stranger can replay.`,
      turnId: `${key}#choose:${index}`,
      origin,
    });
    if (!approved) return refuse("consent denied");

    // The real verified turn: advance. The world fails closed on an illegal move.
    let res: { ok?: boolean; passage?: string; receiptCount?: number; commitmentHex?: string; error?: string };
    try {
      res = JSON.parse(w.advance(index));
    } catch (e) {
      return refuse(String((e as Error)?.message ?? e));
    }
    if (!res.ok) return refuse(res.error || "advance rejected");

    const verified = w.verify();
    return {
      ok: true,
      tier: "extension",
      refused: false,
      verified,
      passage: String(res.passage ?? w.currentPassage()),
      receiptCount: Number(res.receiptCount ?? w.receiptCount()),
      commitment: String(res.commitmentHex ?? w.commitmentHex()),
    };
  }

  /** VERIFY — the LIGHT-CLIENT check a stranger runs: replay the whole receipt
   *  chain from genesis. This is the "a stranger checks the receipt chain" property. */
  private verify(uri: string): StoryVerifyResponse {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    if (!w) return { ok: false, tier: "none", verified: false, error: "not resolved" };
    const verified = w.verify();
    return {
      ok: true,
      tier: verified ? "extension" : "none",
      verified,
      passage: w.currentPassage(),
      commitment: w.commitmentHex(),
      receiptCount: w.receiptCount(),
    };
  }

  // ── COLLECTIVE MODE — the crowd votes each branch; the winner advances ──────

  /** The collective world for an already-resolved uri (or `null` — not resolved /
   *  not a collective world). Fail-closed, exactly like `render`/`verify`. */
  private collectiveWorld(uri: string): CollectiveStoryWorldLike | null {
    const key = canonicalUri(uri);
    const w = key ? this.worlds.get(key) : undefined;
    return w ? asCollective(w) : null;
  }

  /** Parse the world's `[{label, count}]` tally. */
  private parseTally(json: string): BranchTallyRow[] {
    try {
      const rows = JSON.parse(json);
      if (!Array.isArray(rows)) return [];
      return rows.map((r) => ({ label: String(r.label ?? ""), count: Number(r.count ?? 0) }));
    } catch {
      return [];
    }
  }

  /** Parse the world's `openBranchPoll()` `{passage, round, options}`. */
  private branchPoll(w: CollectiveStoryWorldLike): { passage: string; round: number; options: { choiceIndex: number; label: string }[] } {
    try {
      const p = JSON.parse(w.openBranchPoll());
      const options = Array.isArray(p?.options)
        ? p.options.map((o: { choiceIndex?: number; label?: string }, i: number) => ({ choiceIndex: Number(o.choiceIndex ?? i), label: String(o.label ?? "") }))
        : [];
      return { passage: String(p?.passage ?? w.currentPassage()), round: Number(p?.round ?? 0), options };
    } catch {
      return { passage: w.currentPassage(), round: 0, options: [] };
    }
  }

  /** The stable collective voter id (the custody public key), or `null` (no custody). */
  private async resolveVoter(): Promise<string | null> {
    const vi = this.deps.voterIdentity;
    if (!vi) return null;
    try {
      const id = await vi();
      return id && String(id).length > 0 ? String(id) : null;
    } catch {
      return null;
    }
  }

  /** OPEN-BRANCH — the FREE READ tier: the branch poll (options + live tally + prose).
   *  Needs NO custody; a bare browser SEES the passage and the running vote. */
  private async openBranch(uri: string): Promise<StoryOpenBranchResponse> {
    const key = canonicalUri(uri);
    if (!key) return { ok: false, tier: "none", error: "not a dregg-thing" };
    const base = await this.world(key);
    if (!base) return { ok: false, tier: "none", error: "could not resolve story" };
    const w = asCollective(base);
    if (!w) return { ok: false, tier: "none", error: "story is not collective" };
    // Never render a story whose receipt chain does not replay (fail-closed).
    if (!w.verify()) return { ok: false, tier: "none", error: "unverified" };
    const poll = this.branchPoll(w);
    const tally = this.parseTally(w.branchTally());
    const options: BranchOption[] = poll.options.map((o, i) => ({
      choiceIndex: o.choiceIndex,
      label: o.label,
      count: Number(tally[i]?.count ?? 0),
    }));
    const total = options.reduce((a, o) => a + o.count, 0);
    return {
      ok: true,
      tier: "extension",
      passage: poll.passage,
      round: poll.round,
      prose: w.passageProse(),
      options,
      tally,
      total,
      custody: this.hasCustody,
      verified: w.verify(),
      ended: options.length === 0,
    };
  }

  /** BRANCH-TALLY — the FREE READ tier: just the running counts. No custody. */
  private branchTallyOp(uri: string): StoryBranchTallyResponse {
    const w = this.collectiveWorld(uri);
    if (!w) return { ok: false, tier: "none", error: "not resolved" };
    if (!w.verify()) return { ok: false, tier: "none", error: "unverified" };
    const tally = this.parseTally(w.branchTally());
    return { ok: true, tier: "extension", tally, total: tally.reduce((a, r) => a + r.count, 0) };
  }

  /** CAST-BRANCH-VOTE — THE CUSTODY WRITE. A vote is a real verified turn, so it
   *  routes through the injected consent (the faithful reading of the vote-turn)
   *  BEFORE `castVote`, and is recorded under the custody provider's public key.
   *  FAILS CLOSED without prompting on: no custody, no voter id, an invalid option.
   *  A double-vote (one vote per voter) is refused by the world, surfaced honestly. */
  private async castBranchVote(uri: string, optionIndex: number, origin?: string): Promise<StoryBranchVoteResponse> {
    const key = canonicalUri(uri);
    const w = this.collectiveWorld(uri);
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };

    const tallyNow = () => this.parseTally(w.branchTally());
    const refuse = (reason: string): StoryBranchVoteResponse => ({
      ok: true,
      tier: w.verify() ? "extension" : "none",
      refused: true,
      reason,
      tally: tallyNow(),
      total: tallyNow().reduce((a, r) => a + r.count, 0),
    });

    // CUSTODY: casting is a write. No consent provider ⇒ read-only.
    if (!this.hasCustody) return refuse("no custody — connect your cipherclerk to vote");
    // The stable voter id (the custody public key). No id ⇒ fail closed.
    const voter = await this.resolveVoter();
    if (!voter) return refuse("no custody — connect your cipherclerk to vote");

    // FAIL-CLOSED on an option that is not on the open branch — BEFORE any prompt.
    const poll = this.branchPoll(w);
    const option = poll.options.find((o) => o.choiceIndex === optionIndex);
    if (!option) return refuse("no such option");

    // Custody consent (the load-bearing property): the faithful reading the page
    // cannot overlay or clickjack. Every vote is a real turn, so every vote asks.
    const spec = this.specs.get(key)!;
    const approved = await this.deps.consent!({
      explanation:
        `Cast your collective vote for "${option.label}" in the branch poll of story ${spec.addr} ` +
        `(round ${poll.round}, passage "${poll.passage}"). This commits ONE verified vote (one voter, one vote) to the tally.`,
      turnId: `${key}#vote:${poll.round}:${optionIndex}:${voter}`,
      origin,
    });
    if (!approved) return refuse("consent denied");

    // The real cap-gated vote-turn. The world refuses a double-vote (fail-closed).
    let res: { ok?: boolean; tally?: BranchTallyRow[]; error?: string };
    try {
      res = JSON.parse(w.castVote(voter, optionIndex));
    } catch (e) {
      return refuse(String((e as Error)?.message ?? e));
    }
    const tally = Array.isArray(res.tally)
      ? res.tally.map((r) => ({ label: String(r.label ?? ""), count: Number(r.count ?? 0) }))
      : tallyNow();
    if (!res.ok) return { ok: true, tier: "extension", refused: true, reason: res.error || "vote refused", tally, total: tally.reduce((a, r) => a + r.count, 0) };
    return { ok: true, tier: "extension", refused: false, tally, total: tally.reduce((a, r) => a + r.count, 0), voter };
  }

  /** CLOSE-BRANCH — resolve the poll → advance the winner as ONE real verified turn.
   *  Advancing moves the boundary, so it is custody-gated (consent BEFORE any commit),
   *  fail-closed on no custody. A tie is resolved by lowest index and reported HONESTLY. */
  private async closeBranch(uri: string, origin?: string): Promise<StoryCloseBranchResponse> {
    const key = canonicalUri(uri);
    const w = this.collectiveWorld(uri);
    if (!key || !w) return { ok: false, tier: "none", error: "not resolved" };

    const refuse = (reason: string): StoryCloseBranchResponse => ({
      ok: true,
      tier: w.verify() ? "extension" : "none",
      refused: true,
      reason,
      tally: this.parseTally(w.branchTally()),
      passage: w.currentPassage(),
      receiptCount: w.receiptCount(),
      commitment: w.commitmentHex(),
      verified: w.verify(),
    });

    if (!this.hasCustody) return refuse("no custody — connect your cipherclerk to close the branch");

    const spec = this.specs.get(key)!;
    const poll = this.branchPoll(w);
    const approved = await this.deps.consent!({
      explanation:
        `Close the branch poll of story ${spec.addr} (round ${poll.round}, passage "${poll.passage}") ` +
        `and ADVANCE the winning choice as ONE verified turn that binds the new story commitment into the receipt a stranger can replay.`,
      turnId: `${key}#close:${poll.round}`,
      origin,
    });
    if (!approved) return refuse("consent denied");

    let res: {
      ok?: boolean;
      winningChoice?: number;
      winningLabel?: string;
      tie?: boolean;
      tally?: BranchTallyRow[];
      passage?: string;
      receiptCount?: number;
      commitmentHex?: string;
      error?: string;
    };
    try {
      res = JSON.parse(w.closeBranchPoll());
    } catch (e) {
      return refuse(String((e as Error)?.message ?? e));
    }
    if (!res.ok) return refuse(res.error || "close rejected");

    const tally = Array.isArray(res.tally)
      ? res.tally.map((r) => ({ label: String(r.label ?? ""), count: Number(r.count ?? 0) }))
      : this.parseTally(w.branchTally());
    return {
      ok: true,
      tier: "extension",
      refused: false,
      winningChoice: Number(res.winningChoice ?? -1),
      winningLabel: String(res.winningLabel ?? ""),
      tie: !!res.tie,
      tally,
      passage: String(res.passage ?? w.currentPassage()),
      receiptCount: Number(res.receiptCount ?? w.receiptCount()),
      commitment: String(res.commitmentHex ?? w.commitmentHex()),
      verified: w.verify(),
    };
  }
}
