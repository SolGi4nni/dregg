// Logic test for the NETLAYER — the real substrate resolver behind the
// quiet-upgrade port (src/netlayer.ts). Mirrors the client-side verification
// chain of `starbridge-web-surface/src/web_of_cells.rs`
// (`AttestedResource::verify` / `verify_anchored`), asserting each gate BITES.
//
// There is no live node in this harness, so we drive the REAL Netlayer with a
// STAND-IN transport that serves content-addressed bytes + a receipt/proof, and a
// deterministic crypto (sha256 for the content-addressing digest, a checkable
// signature for the committee gate). The LOGIC under test is the shipping code
// path — the content-hash gate, the receipt-in-stream gate, the receipt-stream
// root reconstruction, and the committee-anchored quorum gate — not a live server.
//
// THE LOAD-BEARING PROPERTY (untrusted transport): a hostile gateway that
// SUBSTITUTES the served bytes is REFUSED, because the recomputed digest no longer
// equals the address the client asked for. The addr IS the hash.
//
// Run:  node --test tests/netlayer/run.mjs

import { test } from "node:test";
import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const EXT_ROOT = path.resolve(__dirname, "..", "..");

// Bundle the REAL netlayer module (+ its port.ts imports) to ESM in-memory and
// import it via a data: URL — no generated file touches the tree (mirrors the
// other harnesses' write:false bundling).
async function loadModule(rel) {
  const out = await esbuild.build({
    entryPoints: [path.join(EXT_ROOT, "src", rel)],
    bundle: true,
    format: "esm",
    platform: "neutral",
    target: ["es2022"],
    write: false,
  });
  const b64 = Buffer.from(out.outputFiles[0].text, "utf8").toString("base64");
  return import(`data:text/javascript;base64,${b64}`);
}

async function loadNetlayer() {
  return loadModule("netlayer.ts");
}

// The port module carries the `StoryEngine` + `defaultResolveStory` — bundled so the
// story-netlayer test drives the SAME wiring `getStoryEngine` uses in production
// (`resolveStory: netlayerResolveStory(net)`), minting a world from the verified scene.
async function loadPort() {
  return loadModule("port.ts");
}

// ── the deterministic crypto (real cryptographic hash — the property is genuine) ──
const sha256Hex = (text) => createHash("sha256").update(text, "utf8").digest("hex");
// A checkable stand-in signature: a signer's signature over `msg` is verifiable
// iff it equals this token (so a forged/foreign signature is genuinely rejected).
const signWith = (signer, msg) => `sig::${signer}::${msg}`;
const crypto = {
  hashHex: (text) => sha256Hex(text),
  verifySig: (signer, msg, sig) => sig === signWith(signer, msg),
};

const COMMITTEE = ["vk_alice", "vk_bob", "vk_carol"];

// Build a VALID attested envelope for `contentText`, addressed by its real digest.
// `receiptStreamRootOf` is imported from the module under test so the envelope is
// built the SAME way the Netlayer reconstructs it (a tamper changes the root).
async function makeObject(NL, contentText, { signers = COMMITTEE, threshold = 2, extraLeaves = ["r_x", "r_y"] } = {}) {
  const digest = sha256Hex(contentText);
  const addr = `b3_${digest}`;
  const receiptHash = `r_serve_${digest.slice(0, 8)}`;
  const receiptSet = [...extraLeaves, receiptHash];
  const receiptStreamRoot = await NL.receiptStreamRootOf(receiptSet, crypto.hashHex);
  const quorumSignatures = signers.map((s) => ({ signer: s, sig: signWith(s, receiptStreamRoot) }));
  const env = {
    contentText,
    contentHash: digest,
    receiptHash,
    receiptSet,
    attestedRoot: { receiptStreamRoot, threshold, quorumSignatures },
  };
  return { addr, env, receiptStreamRoot };
}

// A stand-in transport: a canonical-uri → envelope map (the UNTRUSTED hop).
function mapTransport(entries) {
  return (target) => entries.get(target.canonical) ?? null;
}

test("netlayer: content-hash MATCHES addr → verified (extension tier), object + receipt returned", async () => {
  const NL = await loadNetlayer();
  const body = JSON.stringify({ kind: "poll", numOptions: 3, quorumM: 2 });
  const { addr, env } = await makeObject(NL, body);
  const uri = `dregg://poll/${addr}`;
  const net = new NL.Netlayer(mapTransport(new Map([[uri, env]])), crypto, { committee: COMMITTEE });

  const r = await net.resolve(uri);
  assert.equal(r.ok, true, "resolve ok");
  assert.equal(r.verified, true, "verified");
  assert.equal(r.tier, "extension", "tier reflects real verification");
  assert.equal(r.object.addr, addr, "addr echoed");
  assert.deepEqual(r.object.json, { kind: "poll", numOptions: 3, quorumM: 2 }, "verified object body parsed");
  assert.equal(r.receipt.quorum, "anchored", "committee-anchored quorum path");
  assert.equal(r.receipt.receiptCount, env.receiptSet.length, "receipt count surfaced");
});

// ── THE UNTRUSTED-TRANSPORT PROPERTY — a hostile gateway CANNOT substitute content ──
test("netlayer: served bytes DON'T hash to the addr → REFUSED (hostile gateway defeated)", async () => {
  const NL = await loadNetlayer();
  const realBody = JSON.stringify({ kind: "poll", numOptions: 3, quorumM: 2 });
  const { addr, env } = await makeObject(NL, realBody);
  const uri = `dregg://poll/${addr}`;

  // The gateway keeps the ADDRESS the client asked for, but swaps the BYTES (and
  // even lies about contentHash to try to pass its own self-consistency check).
  const forgedText = JSON.stringify({ kind: "poll", numOptions: 99, quorumM: 1 });
  const hostile = { ...env, contentText: forgedText, contentHash: sha256Hex(forgedText) };
  const net = new NL.Netlayer(mapTransport(new Map([[uri, hostile]])), crypto, { committee: COMMITTEE });

  const r = await net.resolve(uri);
  assert.equal(r.ok, false, "hostile substitution refused");
  assert.equal(r.verified, false, "not verified");
  assert.equal(r.tier, "none", "no trust tier on a refused resolve");
  assert.equal(r.errorKind, "content-hash-mismatch", "refused by the content-addressed gate");
  assert.equal(r.object, undefined, "NO object bytes returned on refusal (fail-closed)");
});

test("netlayer: unverifiable receipt/proof → REFUSED (each gate bites)", async () => {
  const NL = await loadNetlayer();
  const body = JSON.stringify({ kind: "poll", numOptions: 2, quorumM: 1 });

  // (a) serve-receipt not a leaf of the committed set.
  {
    const { addr, env } = await makeObject(NL, body);
    const uri = `dregg://poll/${addr}`;
    const bad = { ...env, receiptHash: "r_not_in_set" };
    const net = new NL.Netlayer(mapTransport(new Map([[uri, bad]])), crypto, { committee: COMMITTEE });
    const r = await net.resolve(uri);
    assert.equal(r.verified, false, "receipt-not-in-stream refused");
    assert.equal(r.errorKind, "receipt-not-in-stream");
  }

  // (b) receipt set tampered → recomputed stream root ≠ the signed root.
  {
    const { addr, env } = await makeObject(NL, body);
    const uri = `dregg://poll/${addr}`;
    const tamperedSet = [...env.receiptSet, "r_injected"];
    const bad = { ...env, receiptSet: tamperedSet, receiptHash: env.receiptHash };
    const net = new NL.Netlayer(mapTransport(new Map([[uri, bad]])), crypto, { committee: COMMITTEE });
    const r = await net.resolve(uri);
    assert.equal(r.verified, false, "receipt-stream root mismatch refused");
    assert.equal(r.errorKind, "receipt-stream-root-mismatch");
  }

  // (c) forged committee signatures (signed by attacker-chosen keys) → unattested.
  {
    const forged = await makeObject(NL, body, { signers: ["vk_evil1", "vk_evil2"], threshold: 2 });
    const uri = `dregg://poll/${forged.addr}`;
    const net = new NL.Netlayer(mapTransport(new Map([[uri, forged.env]])), crypto, { committee: COMMITTEE });
    const r = await net.resolve(uri);
    assert.equal(r.verified, false, "forged (non-committee) quorum refused");
    assert.equal(r.errorKind, "unattested", "the committee-anchored gate refuses attacker keys");
  }

  // (d) degenerate threshold:0 / empty-signature root on the same-fed structural
  //     path (no committee configured) → no-quorum (LC-1: threshold:0 is never trust).
  {
    const { addr, env } = await makeObject(NL, body, { threshold: 0, signers: [] });
    const uri = `dregg://poll/${addr}`;
    const net = new NL.Netlayer(mapTransport(new Map([[uri, env]])), crypto, {}); // no committee
    const r = await net.resolve(uri);
    assert.equal(r.verified, false, "degenerate quorum refused");
    assert.equal(r.errorKind, "no-quorum");
  }
});

test("netlayer: malformed content address fails closed (never fetched, never rendered)", async () => {
  const NL = await loadNetlayer();
  const net = new NL.Netlayer(() => { throw new Error("transport must not be reached"); }, crypto, {});
  const r = await net.resolve("dregg://poll/notahash");
  assert.equal(r.verified, false, "a bad addr is refused before any fetch");
  assert.equal(r.errorKind, "bad-addr");
});

// ── the bridge: a verified resolve becomes a PollSpec; a hostile one becomes null ──
test("netlayer bridge: netlayerResolveObject yields a PollSpec iff verified (fail-closed)", async () => {
  const NL = await loadNetlayer();
  const body = JSON.stringify({ kind: "poll", numOptions: 4, quorumM: 3 });
  const { addr, env } = await makeObject(NL, body);
  const uri = `dregg://poll/${addr}`;
  const net = new NL.Netlayer(mapTransport(new Map([[uri, env]])), crypto, { committee: COMMITTEE });
  const resolveObject = NL.netlayerResolveObject(net);

  const spec = await resolveObject(uri);
  assert.deepEqual(spec, { kind: "poll", addr, numOptions: 4, quorumM: 3 }, "verified poll → PollSpec");

  // A hostile substitution ⇒ the bridge returns null (no fabricated poll shape).
  const forgedText = JSON.stringify({ kind: "poll", numOptions: 2, quorumM: 1 });
  const hostile = { ...env, contentText: forgedText, contentHash: sha256Hex(forgedText) };
  const net2 = new NL.Netlayer(mapTransport(new Map([[uri, hostile]])), crypto, { committee: COMMITTEE });
  const spec2 = await NL.netlayerResolveObject(net2)(uri);
  assert.equal(spec2, null, "hostile transport ⇒ null (fail-closed) — never the FNV-shaped stand-in");
});

// ═══════════════════════════════════════════════════════════════════════════
// THE STORY NETLAYER — `dregg://story/<addr>` → a content-addressed, VERIFIED
// `.scene` SOURCE that mints a `StoryWorld` BEFORE it plays. The load-bearing
// property is identical to the object bridge: the untrusted transport carries the
// scene bytes but CANNOT substitute a different story — a swapped scene hashes to a
// different addr and the content-addressed gate refuses it (no scene, no world).
// ═══════════════════════════════════════════════════════════════════════════

// A minimal stand-in `StoryWorld` whose ctor COMPILES the verified scene source (a
// JSON `{ start, prose }`), exactly as the real wasm `StoryWorld::new(scene)` does —
// FAIL-CLOSED: an unparseable scene throws, minting no world.
class StandInStoryWorld {
  constructor(scene) {
    const s = JSON.parse(scene); // throws on a non-scene → fail-closed ctor
    if (!s || typeof s.start !== "string") throw new Error("not a scene");
    this._passage = s.start;
    this._prose = String(s.prose ?? "");
  }
  currentPassage() { return this._passage; }
  passageProse() { return this._prose; }
  choicesJson() { return "[]"; }
  advance() { return JSON.stringify({ ok: false, error: "no choice" }); }
  verify() { return true; }
  commitmentHex() { return "00"; }
  receiptCount() { return 0; }
}

// The canonical `.scene` SOURCE the transport serves; its addr IS its blake3.
const SCENE_SOURCE = JSON.stringify({ start: "clearing", prose: "You stand at a fork." });

test("story netlayer: content-hash MATCHES addr → verified scene returned + a StoryWorld mints", async () => {
  const NL = await loadNetlayer();
  const port = await loadPort();
  const { addr, env } = await makeObject(NL, SCENE_SOURCE);
  const uri = `dregg://story/${addr}`;
  const net = new NL.Netlayer(mapTransport(new Map([[uri, env]])), crypto, { committee: COMMITTEE });

  // The bridge yields a StorySpec carrying the VERIFIED scene (addr == blake3(scene)).
  const spec = await NL.netlayerResolveStory(net)(uri);
  assert.deepEqual(spec, { kind: "story", addr, scene: SCENE_SOURCE }, "verified story → StorySpec with the scene source");

  // And the SAME wiring `getStoryEngine` uses mints a real world from that scene.
  const engine = new port.StoryEngine({ StoryWorld: StandInStoryWorld, resolveStory: NL.netlayerResolveStory(net) });
  const r = await engine.handle({ op: "resolveStory", uri });
  assert.equal(r.ok, true, "story resolved");
  assert.equal(r.verified, true, "verified");
  assert.equal(r.tier, "extension", "extension tier on a verified story");
  assert.equal(r.passage, "clearing", "the world minted from the verified scene (passage from the scene source)");
});

// ── THE UNTRUSTED-TRANSPORT PROPERTY — a hostile gateway CANNOT swap the story ──
test("story netlayer: served bytes DON'T hash to the addr → REFUSED (no scene, no world — hostile story defeated)", async () => {
  const NL = await loadNetlayer();
  const port = await loadPort();
  const { addr, env } = await makeObject(NL, SCENE_SOURCE);
  const uri = `dregg://story/${addr}`;

  // The gateway keeps the ADDRESS the client asked for but swaps the SCENE (and lies
  // about contentHash to try to pass its own self-consistency check).
  const forgedScene = JSON.stringify({ start: "trap", prose: "A pit opens beneath you." });
  const hostile = { ...env, contentText: forgedScene, contentHash: sha256Hex(forgedScene) };
  const net = new NL.Netlayer(mapTransport(new Map([[uri, hostile]])), crypto, { committee: COMMITTEE });

  const spec = await NL.netlayerResolveStory(net)(uri);
  assert.equal(spec, null, "content-hash-mismatch ⇒ null (no scene returned) — the substituted story is refused");

  // Through the engine: no world mints, and the resolve fails closed (never plays).
  const engine = new port.StoryEngine({ StoryWorld: StandInStoryWorld, resolveStory: NL.netlayerResolveStory(net) });
  const r = await engine.handle({ op: "resolveStory", uri });
  assert.equal(r.ok, false, "hostile story fails closed (no world minted)");
  assert.equal(r.verified, false, "not verified");
  assert.equal(r.tier, "none", "no trust tier on a refused story");
});

test("story netlayer: malformed content address fails closed (never fetched, never minted)", async () => {
  const NL = await loadNetlayer();
  const net = new NL.Netlayer(() => { throw new Error("transport must not be reached"); }, crypto, {});
  const spec = await NL.netlayerResolveStory(net)("dregg://story/notahash");
  assert.equal(spec, null, "a bad addr is refused before any fetch (fail-closed, transport untouched)");
});
