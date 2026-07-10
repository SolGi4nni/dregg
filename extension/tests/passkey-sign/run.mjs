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
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import path from "node:path";
import * as esbuild from "esbuild";
import { chromium } from "playwright";

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
