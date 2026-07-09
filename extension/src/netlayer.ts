/**
 * THE NETLAYER — the real substrate resolver behind the quiet-upgrade port.
 *
 * DREGG-QUIET-UPGRADE.md §0–3 + DREGG-WEB-SPEC.md §9.1: a `dregg://<cell>` link
 * is not a *location* but a *capability into a specific cell*; resolving it is a
 * **verified cross-cell read** that returns **attested content**. The transport
 * (Twitter, a gateway, any HTTP host) is UNTRUSTED — it carries the reference and
 * hands back bytes, but it cannot forge the object (content-addressed) and cannot
 * fake the attestation (proof-checked client-side).
 *
 * This module retires the in-memory stand-ins (`defaultResolveObject`'s FNV shape,
 * `MapWebOfCells`) with the CLIENT-SIDE verification chain that
 * `starbridge-web-surface/src/web_of_cells.rs` `AttestedResource::verify` /
 * `verify_anchored` runs, in the same order, each a fail-closed gate:
 *
 *   1. `blake3(content_bytes) == addr`  — the content-addressed gate (MANDATORY:
 *      the addr IS the hash; a hostile gateway that substitutes content is caught
 *      here, because the recomputed digest no longer equals the address we asked
 *      for). This is the whole reason the transport can be untrusted.
 *   2. `receipt_hash ∈ receipt_set`     — the serve-receipt that produced these
 *      bytes is in the attested stream.
 *   3. recomputed receipt-stream root == the root the federation signed
 *      (`verify_receipt_stream` shape).
 *   4. committee-anchored quorum        — cross-fed: the quorum signatures verify
 *      under the client's TRUSTED committee (from genesis/checkpoint config, NEVER
 *      read from the fetched resource), meeting the threshold (`is_valid` shape).
 *      This is F3's just-landed anchored gate. Same-fed (no committee configured)
 *      runs the structural quorum gate (`verify` shape).
 *
 * FAIL-CLOSED throughout: a hash mismatch, a receipt not in the stream, a root
 * mismatch, or an unanchored/forged quorum returns `{ verified:false, tier:"none" }`
 * and NEVER the bytes. Only when every gate holds is `tier:"extension"`.
 *
 * Dependency-free (no `chrome`, no wasm import): the background constructs a
 * `Netlayer` with a real HTTPS transport + a wasm-backed crypto; a test constructs
 * it with a stand-in transport + a deterministic crypto and drives the IDENTICAL
 * verification logic. The crypto primitives (content hash, signature check) are
 * injected; the verification LOGIC lives here and is what the test bites.
 */

import { parseDreggUri, type TrustTier } from "./port";

// ── the attested envelope — the one wire object (mirror of `AttestedResource`) ──
/** A federation attestation over a receipt stream (mirror of `dregg_types::AttestedRoot`). */
export interface AttestedRootWire {
  /** The quorum-signed Merkle root over the committed receipt-hash set (hex). */
  receiptStreamRoot: string;
  /** The Ed25519 quorum threshold — distinct valid signers required (0 ⇒ degenerate). */
  threshold: number;
  /** The quorum signatures: each a `(signer pubkey hex, signature)` over the root. */
  quorumSignatures: Array<{ signer: string; sig: string }>;
  /** A BLS threshold-QC marker. Present ⇒ the anchored gate REFUSES (QC-only can't
   *  be committee-checked here — mirrors `verify_anchored`'s QC refusal). */
  thresholdQc?: unknown;
}

/** The attested-content envelope a `dregg://` fetch returns (mirror of `AttestedResource`).
 *  Every field is a CLAIM by the untrusted transport; the Netlayer verifies each. */
export interface AttestedEnvelope {
  /** The object body as canonical UTF-8 text (dregg objects are canonical text). */
  contentText: string;
  /** The transport's CLAIMED `blake3(contentText)` (hex). Verified against the
   *  recomputed digest AND the requested addr — never trusted. */
  contentHash: string;
  /** The hash of the serve-receipt that committed this content (hex leaf). */
  receiptHash: string;
  /** The committed receipt-hash set (the Merkle leaves) the federation signed. */
  receiptSet: string[];
  /** The genuine federation attestation over the receipt stream. */
  attestedRoot: AttestedRootWire;
}

// ── the untrusted transport hop (HTTPS/WSS to a node/gateway) ────────────────
/** A resolved reference the transport was asked to fetch. */
export interface FetchTarget {
  kind: string;
  /** The content address (`b3_<hex>` form as it appears in the uri). */
  addr: string;
  /** The optional `/field` selector (`dregg://<cell>/field`). */
  field?: string;
  /** The canonical uri key. */
  canonical: string;
}
/** The transport: fetch the attested envelope for a target, or `null` (dead ref).
 *  This is the UNTRUSTED hop — whatever it returns is verified before use. */
export type NetlayerTransport = (target: FetchTarget) => Promise<AttestedEnvelope | null> | AttestedEnvelope | null;

// ── the injected crypto primitives (real wasm in prod, deterministic in test) ─
export interface NetlayerCrypto {
  /** The content-addressing digest: hex `blake3(text)` in production. The addr IS
   *  this digest, so this is the load-bearing untrusted-transport gate. */
  hashHex(text: string): Promise<string> | string;
  /** Verify one quorum signature (`sig` over `msg` by `signer` pubkey). Only
   *  consulted on the committee-anchored path; may be omitted for same-fed. */
  verifySig?(signer: string, msg: string, sig: string): Promise<boolean> | boolean;
}

// ── the acceptance anchor: the client's TRUSTED committee (config, never fetched) ─
export interface NetlayerConfig {
  /** The trusted validator pubkeys from genesis/checkpoint config. When present +
   *  non-empty, a cross-fed resolve runs the committee-anchored gate; when empty,
   *  a same-fed resolve runs the structural quorum gate. NEVER from the resource. */
  committee?: string[];
}

// ── the verdict ──────────────────────────────────────────────────────────────
export type NetlayerErrorKind =
  | "not-a-dregg-thing"
  | "bad-addr"
  | "origin-not-found"
  | "content-hash-mismatch"
  | "receipt-not-in-stream"
  | "receipt-stream-root-mismatch"
  | "no-quorum"
  | "unattested";

/** A resolved object: the verified body text + its parsed JSON (if it parses). */
export interface ResolvedObject {
  kind: string;
  addr: string;
  field?: string;
  /** The verified content bytes as text (the bytes whose blake3 == addr). */
  text: string;
  /** `JSON.parse(text)` when the body is JSON, else `undefined`. */
  json?: unknown;
}
/** The verified receipt/proof carried alongside a resolved object. */
export interface ResolvedReceipt {
  receiptHash: string;
  receiptCount: number;
  receiptStreamRoot: string;
  /** How the quorum was accepted: committee-anchored (cross-fed) or structural (same-fed). */
  quorum: "anchored" | "structural";
}
export interface NetlayerResult {
  ok: boolean;
  verified: boolean;
  tier: TrustTier;
  object?: ResolvedObject;
  receipt?: ResolvedReceipt;
  error?: string;
  errorKind?: NetlayerErrorKind;
}

const VALID_ADDR_RE = /^b3_[0-9a-f]{6,}$/i;

/**
 * THE NETLAYER. Resolves `dregg://<cell>[/field]` to a verified object + receipt,
 * or refuses (fail-closed). Runs only in the extension (background) context.
 */
export class Netlayer {
  constructor(
    private transport: NetlayerTransport,
    private crypto: NetlayerCrypto,
    private config: NetlayerConfig = {},
  ) {}

  /** Resolve + verify a `dregg://<cell>[/field]` uri. */
  async resolve(uri: string): Promise<NetlayerResult> {
    const target = parseTarget(uri);
    if (!target) return refuse("not-a-dregg-thing", "not a dregg-thing");
    if (!VALID_ADDR_RE.test(target.addr)) return refuse("bad-addr", "malformed content address");

    let env: AttestedEnvelope | null;
    try {
      env = await this.transport(target);
    } catch (e) {
      return refuse("origin-not-found", `transport error: ${String((e as Error)?.message ?? e)}`);
    }
    if (!env) return refuse("origin-not-found", "no object at that reference");

    // (1) THE CONTENT-ADDRESSED GATE (MANDATORY). Recompute the digest of the
    // SERVED bytes and require it equals BOTH the transport's claimed hash AND the
    // address we asked for. A hostile gateway that substitutes content produces a
    // different digest → refused. The addr IS the hash: this is what lets the
    // transport be untrusted.
    const addrHex = target.addr.slice(3).toLowerCase();
    const recomputed = (await this.crypto.hashHex(env.contentText)).toLowerCase();
    if (recomputed !== addrHex) {
      return refuse("content-hash-mismatch", "served bytes do not hash to the address (untrusted transport)");
    }
    if (recomputed !== (env.contentHash || "").toLowerCase()) {
      return refuse("content-hash-mismatch", "content hash claim does not match the bytes");
    }

    // (2) the serve-receipt is in the committed set.
    if (!env.receiptSet.includes(env.receiptHash)) {
      return refuse("receipt-not-in-stream", "serve-receipt is not a leaf of the attested stream");
    }

    // (3) the federation's signed root binds exactly this receipt set (recompute).
    const root = await this.receiptStreamRoot(env.receiptSet);
    if (root.toLowerCase() !== (env.attestedRoot.receiptStreamRoot || "").toLowerCase()) {
      return refuse("receipt-stream-root-mismatch", "recomputed receipt-stream root ≠ the signed root");
    }

    // (4) the quorum gate.
    const quorum = await this.checkQuorum(env.attestedRoot);
    if (!quorum.ok) return refuse(quorum.kind, quorum.reason);

    const object: ResolvedObject = {
      kind: target.kind,
      addr: target.addr,
      field: target.field,
      text: env.contentText,
      json: tryParseJson(env.contentText),
    };
    const receipt: ResolvedReceipt = {
      receiptHash: env.receiptHash,
      receiptCount: env.receiptSet.length,
      receiptStreamRoot: env.attestedRoot.receiptStreamRoot,
      quorum: quorum.mode,
    };
    return { ok: true, verified: true, tier: "extension", object, receipt };
  }

  /** The quorum gate — committee-anchored (`verify_anchored`) when a trusted
   *  committee is configured, else the structural gate (`verify`). Fail-closed. */
  private async checkQuorum(
    ar: AttestedRootWire,
  ): Promise<{ ok: true; mode: "anchored" | "structural" } | { ok: false; kind: NetlayerErrorKind; reason: string }> {
    const committee = this.config.committee ?? [];
    if (committee.length > 0) {
      // COMMITTEE-ANCHORED (cross-fed, the LC-1 acceptance gate). A QC-only root
      // cannot be committee-checked here → refuse (mirrors verify_anchored).
      if (ar.thresholdQc != null) return { ok: false, kind: "unattested", reason: "QC-only root is not committee-anchored" };
      if (!ar.threshold || ar.threshold <= 0) return { ok: false, kind: "unattested", reason: "no positive threshold" };
      const set = new Set(committee.map((k) => k.toLowerCase()));
      const verify = this.crypto.verifySig;
      if (!verify) return { ok: false, kind: "unattested", reason: "no signature verifier configured for the anchored gate" };
      const seen = new Set<string>();
      for (const s of ar.quorumSignatures) {
        const signer = (s.signer || "").toLowerCase();
        if (!set.has(signer)) continue; // a signature by a non-committee key never counts
        if (seen.has(signer)) continue; // distinct signers only
        if (await verify(s.signer, ar.receiptStreamRoot, s.sig)) seen.add(signer);
      }
      if (seen.size < ar.threshold) {
        return { ok: false, kind: "unattested", reason: "committee quorum not met (forged/insufficient signatures)" };
      }
      return { ok: true, mode: "anchored" };
    }
    // STRUCTURAL (same-fed): a degenerate threshold:0 / empty-signature root is
    // NEVER acceptance (LC-1); a real attestation carries a positive threshold and
    // enough signatures. No committee ⇒ we cannot cryptographically anchor, so this
    // is the count gate `verify` runs.
    if (ar.thresholdQc == null && (!ar.threshold || ar.threshold <= 0 || ar.quorumSignatures.length === 0)) {
      return { ok: false, kind: "no-quorum", reason: "degenerate / empty quorum" };
    }
    if (ar.thresholdQc == null && ar.quorumSignatures.length < ar.threshold) {
      return { ok: false, kind: "no-quorum", reason: "signature count below threshold" };
    }
    return { ok: true, mode: "structural" };
  }

  /** Reconstruct the receipt-stream Merkle root from the leaf set (the
   *  `merkle_root_of_receipt_hashes` shape): a binary Merkle tree over the leaves,
   *  each interior node `hashHex(left + right)`. Deterministic in leaf order. */
  private async receiptStreamRoot(receiptSet: string[]): Promise<string> {
    if (receiptSet.length === 0) return this.hash("");
    let level = receiptSet.map((h) => h.toLowerCase());
    while (level.length > 1) {
      const next: string[] = [];
      for (let i = 0; i < level.length; i += 2) {
        const left = level[i];
        const right = i + 1 < level.length ? level[i + 1] : level[i]; // duplicate the last on an odd row
        next.push(await this.hash(left + right));
      }
      level = next;
    }
    return level[0];
  }

  private async hash(text: string): Promise<string> {
    return (await this.crypto.hashHex(text)).toLowerCase();
  }
}

/** The receipt-stream root reconstruction as a free function, so a transport /
 *  test can build a *valid* envelope the exact same way the Netlayer checks it. */
export async function receiptStreamRootOf(
  receiptSet: string[],
  hashHex: (text: string) => Promise<string> | string,
): Promise<string> {
  if (receiptSet.length === 0) return (await hashHex("")).toLowerCase();
  let level = receiptSet.map((h) => h.toLowerCase());
  while (level.length > 1) {
    const next: string[] = [];
    for (let i = 0; i < level.length; i += 2) {
      const left = level[i];
      const right = i + 1 < level.length ? level[i + 1] : level[i];
      next.push((await hashHex(left + right)).toLowerCase());
    }
    level = next;
  }
  return level[0];
}

function parseTarget(uri: string): FetchTarget | null {
  const parsed = parseDreggUri(uri);
  if (!parsed) return null;
  // A `/field` selector attenuates the addr's tail: `dregg://cell/b3_x/body`.
  const slash = parsed.addr.indexOf("/");
  let addr = parsed.addr;
  let field: string | undefined;
  if (slash >= 0) {
    addr = parsed.addr.slice(0, slash);
    field = parsed.addr.slice(slash + 1) || undefined;
  }
  const canonical = `dregg://${parsed.kind}/${parsed.addr}`;
  return { kind: parsed.kind, addr, field, canonical };
}

function tryParseJson(text: string): unknown {
  try {
    return JSON.parse(text);
  } catch {
    return undefined;
  }
}

function refuse(kind: NetlayerErrorKind, error: string): NetlayerResult {
  return { ok: false, verified: false, tier: "none", error, errorKind: kind };
}

// ═══════════════════════════════════════════════════════════════════════════
// THE PRODUCTION CRYPTO — wasm blake3 for content-addressing + WebCrypto Ed25519
// for the committee-anchored gate. Injected into the background's Netlayer.
// ═══════════════════════════════════════════════════════════════════════════

/** The structural wasm surface the netlayer crypto needs. */
export interface NetlayerWasmLike {
  blake3_hash(input: string): string;
}

/** The production crypto: `blake3_hash` from the wasm module for content-addressing,
 *  and WebCrypto Ed25519 for committee signatures (when a committee is anchored). */
export function wasmNetlayerCrypto(wasm: NetlayerWasmLike): NetlayerCrypto {
  return {
    hashHex: (text: string) => wasm.blake3_hash(text),
    async verifySig(signer: string, msg: string, sig: string): Promise<boolean> {
      try {
        const key = await crypto.subtle.importKey("raw", hexToBytes(signer), { name: "Ed25519" }, false, ["verify"]);
        return await crypto.subtle.verify({ name: "Ed25519" }, key, hexToBytes(sig), new TextEncoder().encode(msg));
      } catch {
        return false; // an unverifiable signature never counts (fail-closed)
      }
    },
  };
}

function hexToBytes(hex: string): Uint8Array<ArrayBuffer> {
  const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
  const out = new Uint8Array(new ArrayBuffer(clean.length >> 1));
  for (let i = 0; i < out.length; i++) out[i] = parseInt(clean.substr(i * 2, 2), 16);
  return out;
}

// ═══════════════════════════════════════════════════════════════════════════
// THE PRODUCTION TRANSPORT — HTTPS/WSS to the configured node/gateway.
// The submit lane (`background.ts`) already talks to a node over `nodeUrl`; the
// resolve lane fetches the attested envelope the same way. UNTRUSTED: whatever it
// returns is verified above before a byte reaches a renderer.
// ═══════════════════════════════════════════════════════════════════════════

/** The minimal node-config surface the transport needs (mirror of `NodeConfig`). */
export interface NetlayerNodeConfigLike {
  nodeUrl: string;
  devnetKey?: string;
}

/** A transport that GETs the attested envelope from the node's resolve endpoint.
 *  `GET {nodeUrl}/api/dregg/object/<kind>/<addr>[?field=…]`. Content-addressed →
 *  cacheable and origin-agnostic; a 404 is a dead reference (`null`). */
export function httpsNetlayerTransport(getConfig: () => NetlayerNodeConfigLike): NetlayerTransport {
  return async (target: FetchTarget): Promise<AttestedEnvelope | null> => {
    const cfg = getConfig();
    const base = cfg.nodeUrl.replace(/\/$/, "");
    const q = target.field ? `?field=${encodeURIComponent(target.field)}` : "";
    const url = `${base}/api/dregg/object/${encodeURIComponent(target.kind)}/${encodeURIComponent(target.addr)}${q}`;
    const headers: Record<string, string> = { Accept: "application/json" };
    if (cfg.devnetKey) headers["X-Devnet-Key"] = cfg.devnetKey;
    const resp = await fetch(url, { signal: AbortSignal.timeout(15000), headers });
    if (resp.status === 404) return null;
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    const body = (await resp.json()) as AttestedEnvelope;
    return body;
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// THE BRIDGES — adapt a verified Netlayer resolve into the engine resolver seams
// the `PollEngine` / `CellEngine` already accept. This is the WIRING that retires
// the in-memory stand-ins (`defaultResolveObject`, `MapWebOfCells`) in production:
// the background injects these instead. Every bridge is FAIL-CLOSED — an
// unverified resolve yields `null` / `unresolved`, never a fabricated shape.
// ═══════════════════════════════════════════════════════════════════════════

import type { PollSpec, DocSpec, ResolveObjectFn, ResolveDocFn, ResolveCellFn, ResolveValueFn, CellLookup, ValueQuote, ResolvedCell } from "./port";

/** `PollEngine.resolveObject` over the Netlayer: the verified poll object's body is
 *  canonical JSON `{ kind:"poll", numOptions, quorumM }`. Unverified ⇒ `null`. */
export function netlayerResolveObject(net: Netlayer): ResolveObjectFn {
  return async (uri: string): Promise<PollSpec | null> => {
    const r = await net.resolve(uri);
    if (!r.ok || !r.verified || !r.object) return null;
    const j = r.object.json as { kind?: string; numOptions?: number; quorumM?: number } | undefined;
    if (!j || j.kind !== "poll") return null;
    const numOptions = Number(j.numOptions);
    const quorumM = Number(j.quorumM);
    if (!Number.isInteger(numOptions) || numOptions < 2) return null;
    if (!Number.isInteger(quorumM) || quorumM < 1) return null;
    return { kind: "poll", addr: r.object.addr, numOptions, quorumM };
  };
}

/** `DocEngine.resolveDoc` over the Netlayer: the verified doc object's body is
 *  canonical JSON `{ kind:"doc", stitch? }`. The content-addressed + attested fetch
 *  IS the resolve; an unverified body ⇒ `null` (fail-closed, exactly like the poll
 *  bridge). `stitch` (a concurrent divergence the loaded document already carries)
 *  rides in the verified body — never fabricated here. */
export function netlayerResolveDoc(net: Netlayer): ResolveDocFn {
  return async (uri: string): Promise<DocSpec | null> => {
    const r = await net.resolve(uri);
    if (!r.ok || !r.verified || !r.object) return null;
    const j = r.object.json as { kind?: string; stitch?: boolean } | undefined;
    if (!j || j.kind !== "doc") return null;
    return { kind: "doc", addr: r.object.addr, stitch: j.stitch === true };
  };
}

/** `CellEngine.resolveCell` over the Netlayer: the verified cell body is canonical
 *  JSON `{ html, provenance, inCap }`. A dead ref ⇒ `unresolved` (fail-closed). */
export function netlayerResolveCell(net: Netlayer): ResolveCellFn {
  return async (uri: string): Promise<CellLookup> => {
    const r = await net.resolve(uri);
    if (!r.ok || !r.verified || !r.object) {
      // A name explicitly bound-to-nothing is signalled by the object body; a
      // fetch that returns no verified object is `unresolved`.
      return { found: false, reason: "unresolved" };
    }
    const j = r.object.json as { unbound?: boolean; html?: string; provenance?: ResolvedCell["provenance"]; inCap?: boolean } | undefined;
    if (!j) return { found: false, reason: "unresolved" };
    if (j.unbound === true) return { found: false, reason: "unbound" };
    if (typeof j.html !== "string" || !j.provenance) return { found: false, reason: "unresolved" };
    const cell: ResolvedCell = { html: j.html, provenance: j.provenance, inCap: j.inCap !== false };
    return { found: true, cell };
  };
}

/** `CellEngine.resolveValue` over the Netlayer: a value quote is the verified bytes
 *  of a cited receipt. The Netlayer's proof-check IS the anchored quote verifier —
 *  a body that will not verify never reaches here, so a resolved value is verified. */
export function netlayerResolveValue(net: Netlayer): ResolveValueFn {
  return async (uri: string): Promise<ValueQuote | null> => {
    const r = await net.resolve(uri);
    if (!r.ok || !r.verified || !r.object) return null;
    const j = r.object.json as { bytes?: string; provenance?: ValueQuote["provenance"] } | undefined;
    const bytes = j && typeof j.bytes === "string" ? j.bytes : r.object.text;
    const provenance = (j && j.provenance) || { cell: r.object.addr, receipt: r.receipt?.receiptHash };
    return { bytes, provenance, verified: true };
  };
}
