// Headless-Chromium test for the SIGN PATH through the CustodyProvider seam.
//
// Proves the deliverable: `resolveCustody` (the §4.5 chain background.ts now calls
// to produce the SignedTurn envelope) drives the REAL providers over the REAL dregg
// wasm, with a CDP WebAuthn VIRTUAL AUTHENTICATOR (PRF) for the passkey tier:
//
//   • extension tier — resolves to MnemonicCustody (the phrase re-derives to the
//     identity) and produces a VALID hybrid SignedTurn; its classical perimeter is
//     BYTE-IDENTICAL to the old direct `assemble_signed_turn_envelope(turn, seed)`
//     path, and the mnemonic re-derives to the EXACT stored seed (the seam did not
//     change the extension's signatures);
//   • extension tier, phrase withheld / mismatched — falls back to the byte-exact
//     SeedCustody (still "extension"), classical perimeter byte-identical;
//   • passkey tier — an EXTENSION-LESS resolve (no extension material) authenticates
//     the passkey (PRF) → unwraps → produces a VALID hybrid SignedTurn (signer ==
//     the enrolled dregg key, appears verbatim in the envelope);
//   • no custody — resolve with no extension + no passkey → tier "none", provider
//     null: a write FAILS CLOSED.
//
// Run:  node --test tests/passkey-sign/run.mjs

import { test } from "node:test";
import assert from "node:assert/strict";
import http from "node:http";
import { createPublicKey, verify as edVerify } from "node:crypto";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";
import { blake3 } from "./blake3.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const EXT_ROOT = path.resolve(__dirname, "..", "..");

// The canonical all-zero-entropy 24-word BIP39 mnemonic (valid checksum).
const MNEMONIC =
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon " +
  "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art";

const MIME = {
  ".js": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
  ".html": "text/html; charset=utf-8",
};

const fromB64 = (s) => Uint8Array.from(Buffer.from(s, "base64"));

// FIPS-204 ML-DSA signing is HEDGED, so even two signings with the SAME key over
// the SAME turn diverge inside `pq_signature`. The DETERMINISTIC region (turn ++
// ed25519 sig ++ ed25519 signer ++ the fixed pq-length varint) is byte-identical;
// only the hedged pq tail differs. We therefore establish the deterministic
// boundary empirically (two direct signings' longest-common-prefix) and require
// every provider to match the direct path to that SAME boundary — a classical
// perimeter regression (e.g. a different ed25519 signature) drops the LCP far
// below it. `SLACK` absorbs the ~1 byte the random pq tails may coincidentally
// share on either side.
const SLACK = 16;

async function buildHarness() {
  const out = await esbuild.build({
    entryPoints: [path.join(__dirname, "harness.ts")],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2022"],
    write: false,
  });
  return out.outputFiles[0].text;
}

async function startServer(harnessJs) {
  const fixture = await readFile(path.join(__dirname, "fixture.html"), "utf8");
  const glue = await readFile(path.join(EXT_ROOT, "dregg_wasm.js"), "utf8");
  const wasm = await readFile(path.join(EXT_ROOT, "dregg_wasm_bg.wasm"));
  const server = http.createServer((req, res) => {
    const url = req.url.split("?")[0];
    const send = (body, type) => {
      res.writeHead(200, { "content-type": type });
      res.end(body);
    };
    if (url === "/" || url === "/fixture.html") return send(fixture, MIME[".html"]);
    if (url === "/harness.js") return send(harnessJs, MIME[".js"]);
    if (url === "/dregg_wasm.js") return send(glue, MIME[".js"]);
    if (url === "/dregg_wasm_bg.wasm") return send(wasm, MIME[".wasm"]);
    res.writeHead(404);
    res.end("not found");
  });
  await new Promise((r) => server.listen(0, "127.0.0.1", r));
  const { port } = server.address();
  return { server, base: `http://localhost:${port}` };
}

async function addAuthenticator(client) {
  await client.send("WebAuthn.enable", { enableUI: false });
  const base = {
    protocol: "ctap2",
    ctap2Version: "ctap2_1",
    transport: "internal",
    hasResidentKey: true,
    hasUserVerification: true,
    automaticPresenceSimulation: true,
    isUserVerified: true,
  };
  try {
    const { authenticatorId } = await client.send("WebAuthn.addVirtualAuthenticator", {
      options: { ...base, hasPrf: true },
    });
    return authenticatorId;
  } catch {
    const { authenticatorId } = await client.send("WebAuthn.addVirtualAuthenticator", {
      options: base,
    });
    return authenticatorId;
  }
}

/**
 * Assert a provider's envelope matches the direct path through the entire
 * deterministic region (`boundary` = the direct-vs-direct LCP). Only the hedged
 * FIPS-204 pq tail beyond `boundary` may differ.
 */
async function assertClassicalPerimeterIdentical(page, directB64, providerB64, boundary, label) {
  const r = await page.evaluate(([a, b]) => window.__sign.lcp(a, b), [directB64, providerB64]);
  assert.equal(r.aLen, r.bLen, `${label}: same envelope length as the direct path`);
  assert.ok(
    r.lcp >= boundary - SLACK,
    `${label}: classical perimeter byte-identical (lcp=${r.lcp} >= boundary ${boundary}-${SLACK})`,
  );
}

test("sign path via CustodyProvider: extension byte-identical, passkey signs a real turn, no-custody fails closed", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on("pageerror", (e) => errors.push(String(e)));

    const client = await page.context().newCDPSession(page);
    const authenticatorId = await addAuthenticator(client);

    await page.goto(`${base}/fixture.html`);
    await page.waitForFunction(() => window.__READY === true || window.__ERR, null, { timeout: 30000 });
    const bootErr = await page.evaluate(() => window.__ERR || null);
    assert.equal(bootErr, null, `harness boot error: ${bootErr}`);

    const turnB64 = await page.evaluate((m) => window.__sign.buildTurn(m), MNEMONIC);
    assert.ok(turnB64 && turnB64.length > 0, "built a real normalized turn");
    const rederivedPub = await page.evaluate((m) => window.__sign.rederivePub(m), MNEMONIC);
    const storedSeed = await page.evaluate((m) => window.__sign.deriveSeed(m), MNEMONIC);

    // ── The OLD direct path (assemble over the seed) — the byte-identity baseline.
    const direct = await page.evaluate(
      ([m, t]) => window.__sign.directEnvelope(m, t),
      [MNEMONIC, turnB64],
    );
    // Establish the deterministic boundary: two DIRECT signings of the same key
    // over the same turn share exactly the deterministic prefix, then diverge in
    // the hedged pq tail. (This also proves the pq half is genuinely hedged, so the
    // meaningful byte-identity claim is over the classical perimeter.)
    const direct2 = await page.evaluate(
      ([m, t]) => window.__sign.directEnvelope(m, t),
      [MNEMONIC, turnB64],
    );
    const boundaryProbe = await page.evaluate(([a, b]) => window.__sign.lcp(a, b), [direct, direct2]);
    const boundary = boundaryProbe.lcp;
    assert.ok(boundary > 64 + 32, "deterministic prefix covers at least the ed25519 signature + signer");
    assert.ok(boundary < boundaryProbe.aLen, "two hedged signings still differ in the pq tail (pq is hedged)");

    // ── EXTENSION tier via MnemonicCustody (phrase re-derives to the identity).
    const extMnemonic = await page.evaluate(
      ([m, t]) => window.__sign.resolveExtensionSign(m, t, true),
      [MNEMONIC, turnB64],
    );
    assert.equal(extMnemonic.tier, "extension", "phrase-present resolves to the extension tier");
    assert.equal(extMnemonic.provider, true, "a provider was resolved");
    assert.equal(extMnemonic.label, "Extension cipherclerk", "MnemonicCustody label");
    assert.equal(extMnemonic.signer, rederivedPub, "extension envelope signer == the dregg identity");
    assert.equal(extMnemonic.signerInEnvelope, true, "signer appears verbatim in the envelope");
    // The seam did not change the extension's signatures: mnemonic re-derives to the
    // EXACT stored seed, and the classical perimeter equals the old direct path.
    const remnemSeed = await page.evaluate((m) => window.__sign.deriveSeed(m), MNEMONIC);
    assert.equal(remnemSeed, storedSeed, "MnemonicCustody re-derives the EXACT stored seed (byte-exact key)");
    await assertClassicalPerimeterIdentical(page, direct, extMnemonic.env, boundary, "MnemonicCustody vs direct");

    // ── EXTENSION tier via SeedCustody (phrase withheld) — still byte-exact.
    const extSeed = await page.evaluate(
      ([m, t]) => window.__sign.resolveExtensionSign(m, t, false),
      [MNEMONIC, turnB64],
    );
    assert.equal(extSeed.tier, "extension", "phrase-withheld still resolves to the extension tier");
    assert.equal(extSeed.label, "Extension cipherclerk", "SeedCustody label");
    assert.equal(extSeed.signer, rederivedPub, "SeedCustody envelope signer == the dregg identity");
    assert.equal(extSeed.signerInEnvelope, true, "signer appears verbatim in the SeedCustody envelope");
    await assertClassicalPerimeterIdentical(page, direct, extSeed.env, boundary, "SeedCustody vs direct");

    // ── EXTENSION tier with a MISMATCHED phrase → falls back to SeedCustody, byte-exact.
    const mismatched = await page.evaluate(
      ([m, t]) => window.__sign.resolveMismatchedMnemonic(m, t),
      [MNEMONIC, turnB64],
    );
    assert.equal(mismatched.tier, "extension", "mismatched phrase stays extension tier");
    assert.equal(mismatched.label, "Extension cipherclerk", "mismatched phrase → SeedCustody fallback");
    await assertClassicalPerimeterIdentical(page, direct, mismatched.env, boundary, "mismatch-fallback vs direct");

    // ── NO CUSTODY: resolve with no extension + no passkey → tier none, fail closed.
    const none = await page.evaluate((t) => window.__sign.resolveNoCustody(t), turnB64);
    assert.equal(none.tier, "none", "no material resolves to the none tier");
    assert.equal(none.provider, false, "no provider is returned");
    assert.equal(none.failedClosed, true, "a write with no custody FAILS CLOSED");

    // ── PASSKEY tier (extension-less): enroll then resolve+sign a real turn.
    let e2ePrf = true;
    let enrolled;
    try {
      enrolled = await page.evaluate((m) => window.__sign.enrollPasskey(m), MNEMONIC);
    } catch (err) {
      if (/PRF/i.test(String(err))) {
        e2ePrf = false;
        console.warn("[passkey-sign] PRF could not be virtualized here; asserted extension + no-custody tiers only.");
      } else {
        throw err;
      }
    }

    if (e2ePrf) {
      assert.equal(enrolled.publicKey, rederivedPub, "passkey enrolled the right dregg key");
      const pkSigned = await page.evaluate((t) => window.__sign.resolvePasskeySign(t), turnB64);
      assert.equal(pkSigned.tier, "passkey", "extension-less resolve → passkey tier");
      assert.equal(pkSigned.provider, true, "a passkey provider was resolved");
      assert.equal(pkSigned.label, "Passkey", "PasskeyCustody label");
      assert.ok(pkSigned.len > 64, "passkey produced a non-trivial hybrid SignedTurn");
      assert.equal(pkSigned.signer, rederivedPub, "passkey envelope signer == the enrolled dregg key");
      assert.equal(pkSigned.signerInEnvelope, true, "signer appears verbatim in the passkey envelope");
      // A real turn signed via the passkey is the SAME shape the node accepts: its
      // classical perimeter matches the direct path over the same key.
      await assertClassicalPerimeterIdentical(page, direct, pkSigned.env, boundary, "passkey vs direct");

      // FAIL-CLOSED: clear the authenticator; the extension-less resolve can no
      // longer assert → passkey signTurn refuses.
      await client.send("WebAuthn.clearCredentials", { authenticatorId });
      const pkFail = await page.evaluate(async (t) => {
        try {
          await window.__sign.resolvePasskeySign(t);
          return { failedClosed: false, error: null };
        } catch (e) {
          return { failedClosed: true, error: String((e && e.message) || e) };
        }
      }, turnB64);
      assert.equal(pkFail.failedClosed, true, "passkey signTurn FAILS CLOSED when the authenticator can't assert");
    }

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
    assert.ok(e2ePrf, "the virtual authenticator supported PRF (full passkey resolve→sign ran)");
  } finally {
    await browser.close();
    server.close();
  }
});

// ═══════════════════════════════════════════════════════════════════════════
// signTurnV3 federation-domain bridge (OWNER-LIFECYCLE-BROWSER-SEAM).
//
// Drives the REAL 3-argument wasm `sign_turn_v3(turnBytes, seed, federationId)`
// export over a real Unchecked turn, then verifies each produced Ed25519
// authorization INDEPENDENTLY in Node: the signing message
// (`TurnExecutor::compute_signing_message`, `dregg-action-sig-v2` domain
// separation) is reconstructed here from the signed turn's own fields with a
// vendored single-chunk BLAKE3 (grounded against the wasm blake3 first), and
// node:crypto's Ed25519 does the verification. If the export ignored or
// misapplied its domain argument, verify-under-domain would fail (or
// verify-under-zero would spuriously succeed) — the signature itself is the
// checksum over every reconstruction detail.
// ═══════════════════════════════════════════════════════════════════════════

const DELEGATION_MODE = { None: 0, ParentsOwn: 1, Inherit: 2, SnapshotRefresh: 3 };
const COMMITMENT_MODE = { Full: 0, Partial: 1 };

function concatBytes(arrs) {
  const len = arrs.reduce((n, a) => n + a.length, 0);
  const out = new Uint8Array(len);
  let o = 0;
  for (const a of arrs) { out.set(a, o); o += a.length; }
  return out;
}

/** `Effect::hash()` for the effect shapes this test's turn contains. */
function effectHash(effect) {
  const [name, body] = Object.entries(effect)[0];
  if (name === "IncrementNonce") {
    return blake3(concatBytes([Uint8Array.of(5), Uint8Array.from(body.cell)]));
  }
  throw new Error(`effectHash: unhandled effect variant ${name} — extend the test oracle`);
}

/** postcard of default `Preconditions` (3 Nones + empty witnessed vec). */
function postcardPreconditions(p) {
  if (p.cell_state !== null || p.network !== null || p.valid_while !== null || (p.witnessed || []).length !== 0) {
    throw new Error("test oracle only encodes default Preconditions");
  }
  return Uint8Array.of(0, 0, 0, 0);
}

/** Reconstruct `TurnExecutor::compute_signing_message(action, federationId)`. */
function signingMessage(action, federationId) {
  const parts = [
    new TextEncoder().encode("dregg-action-sig-v2:"),
    federationId,
    Uint8Array.from(action.target),
    Uint8Array.from(action.method),
  ];
  for (const arg of action.args) parts.push(Uint8Array.from(arg));
  for (const eff of action.effects) parts.push(effectHash(eff));
  parts.push(Uint8Array.of(DELEGATION_MODE[action.may_delegate]));
  parts.push(Uint8Array.of(COMMITMENT_MODE[action.commitment_mode]));
  if (action.balance_change === null || action.balance_change === undefined) {
    parts.push(Uint8Array.of(0));
  } else {
    const buf = new Uint8Array(9);
    buf[0] = 1;
    new DataView(buf.buffer).setBigInt64(1, BigInt(action.balance_change), true);
    parts.push(buf);
  }
  parts.push(postcardPreconditions(action.preconditions));
  return blake3(concatBytes(parts));
}

const ED25519_SPKI_PREFIX = Buffer.from("302a300506032b6570032100", "hex");
function ed25519Verify(pubkeyHex, message, sig) {
  const key = createPublicKey({
    key: Buffer.concat([ED25519_SPKI_PREFIX, Buffer.from(pubkeyHex, "hex")]),
    format: "der",
    type: "spki",
  });
  return edVerify(null, Buffer.from(message), key, Buffer.from(sig));
}

/** All ed25519 authorization sigs in a signed turn's call forest (flat walk). */
function forestEd25519Sigs(turn) {
  const sigs = [];
  const walk = (tree) => {
    const auth = tree.action.authorization;
    const sigBytes = auth?.HybridSignature?.ed25519 ?? auth?.Signature;
    assert.ok(sigBytes, "action carries a real signature after sign_turn_v3");
    sigs.push({ action: tree.action, sig: Uint8Array.from(sigBytes) });
    for (const child of tree.children || []) walk(child);
  };
  for (const root of turn.call_forest.roots) walk(root);
  return sigs;
}

test("signTurnV3 federation domain: 00/7f/80/ff round-trip, verify under the signed domain, FAIL under zero / off-by-one", async () => {
  const harnessJs = await buildHarness();
  const { server, base } = await startServer(harnessJs);
  const browser = await chromium.launch({ headless: true });
  try {
    const page = await browser.newPage();
    await page.goto(`${base}/fixture.html`);
    await page.waitForFunction(() => window.__READY === true || window.__ERR, null, { timeout: 30000 });
    assert.equal(await page.evaluate(() => window.__ERR || null), null, "harness booted");

    // ── Ground the vendored JS blake3 against the wasm implementation across
    //    block boundaries BEFORE trusting any reconstruction below.
    for (const n of [0, 1, 31, 32, 63, 64, 65, 127, 128, 129, 200]) {
      const s = "a".repeat(n);
      const js = Buffer.from(blake3(new TextEncoder().encode(s))).toString("hex");
      const rs = await page.evaluate((x) => window.__sign.blake3Hex(x), s);
      assert.equal(js, rs, `vendored blake3 matches wasm at input length ${n}`);
    }

    const turnB64 = await page.evaluate((m) => window.__sign.buildUncheckedTurn(m), MNEMONIC);
    const zero = new Uint8Array(32);

    for (const fill of [0x00, 0x7f, 0x80, 0xff]) {
      const domain = new Uint8Array(32).fill(fill);
      const domainB64 = Buffer.from(domain).toString("base64");
      const signed = await page.evaluate(
        ([m, t, d]) => window.__sign.signTurnV3WithDomain(m, t, d),
        [MNEMONIC, turnB64, domainB64],
      );
      assert.match(signed.turnId, /^[0-9a-f]{64}$/, "canonical turn id");
      const turn = JSON.parse(Buffer.from(fromB64(signed.turnJsonB64)).toString("utf8"));
      const sigs = forestEd25519Sigs(turn);
      assert.ok(sigs.length >= 1, "at least one signed action");

      for (const { action, sig } of sigs) {
        // Round-trip: the signature verifies under EXACTLY the domain signed.
        assert.equal(
          ed25519Verify(signed.signerPubkey, signingMessage(action, domain), sig),
          true,
          `0x${fill.toString(16)}*32: verifies under the signed domain`,
        );
        // Cross-domain refusal: FAILS under zero (unless the domain IS zero) …
        assert.equal(
          ed25519Verify(signed.signerPubkey, signingMessage(action, zero), sig),
          fill === 0x00,
          `0x${fill.toString(16)}*32: under-zero verification is ${fill === 0x00 ? "the same domain" : "refused"}`,
        );
        // … and under a one-byte-different domain (both edges).
        for (const flipAt of [0, 31]) {
          const off = Uint8Array.from(domain);
          off[flipAt] ^= 1;
          assert.equal(
            ed25519Verify(signed.signerPubkey, signingMessage(action, off), sig),
            false,
            `0x${fill.toString(16)}*32: refused under domain with byte ${flipAt} flipped`,
          );
        }
      }
    }

    // ── Backward compatibility: the zero-domain signature (what a one-arg
    //    `dregg.signTurnV3(turnBytes)` call produces) verifies under zero.
    const zeroB64 = Buffer.from(zero).toString("base64");
    const legacy = await page.evaluate(
      ([m, t, d]) => window.__sign.signTurnV3WithDomain(m, t, d),
      [MNEMONIC, turnB64, zeroB64],
    );
    const legacyTurn = JSON.parse(Buffer.from(fromB64(legacy.turnJsonB64)).toString("utf8"));
    for (const { action, sig } of forestEd25519Sigs(legacyTurn)) {
      assert.equal(ed25519Verify(legacy.signerPubkey, signingMessage(action, zero), sig), true,
        "legacy zero-domain signature verifies under zero");
    }

    // ── wasm-level typed rejection: wrong-length domains throw BEFORE signing.
    for (const len of [0, 31, 33]) {
      const bad = await page.evaluate(
        ([m, t, n]) => window.__sign.signTurnV3BadDomain(m, t, n),
        [MNEMONIC, turnB64, len],
      );
      assert.equal(bad.threw, true, `domain length ${len} throws`);
      assert.match(bad.error, /32 bytes/, `domain length ${len} error names the exact-32 requirement`);
    }
  } finally {
    await browser.close();
    server.close();
  }
});
