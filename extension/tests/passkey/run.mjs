// Headless-Chromium test for the PASSKEY CUSTODY floor (extension-less custody).
//
// Uses a CDP WebAuthn VIRTUAL AUTHENTICATOR with the PRF / hmac-secret extension
// (no real biometric) to drive the REAL `PasskeyCustody` over the REAL dregg wasm
// signing path. Asserts the load-bearing properties:
//   • enroll registers a credential + a WRAPPED seed, and the plaintext mnemonic
//     is NOT present in the stored blob (seed-not-in-blob);
//   • the enrolled pubkey equals the mnemonic's independently re-derived pubkey
//     (custody bound the right dregg key);
//   • signTurn authenticates (PRF) → unwraps → produces a HYBRID SignedTurn whose
//     ed25519 signer matches the enrolled pubkey AND appears verbatim in the
//     envelope (the sign path really used the gated key);
//   • a cleared authenticator (wrong/failed auth) → signTurn FAILS CLOSED, no sig,
//     while the wrapped blob alone stays insufficient to sign;
//   • a WRONG wrap secret fails closed (GCM), and the wrap/sign LOGIC round-trips
//     under an injected secret (the PRF-independent contingency the task names).
//
// Run:  node --test tests/passkey/run.mjs

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

function containsSub(hay, needle) {
  if (needle.length === 0 || needle.length > hay.length) return false;
  outer: for (let i = 0; i <= hay.length - needle.length; i++) {
    for (let j = 0; j < needle.length; j++) if (hay[i + j] !== needle[j]) continue outer;
    return true;
  }
  return false;
}
const fromB64 = (s) => Uint8Array.from(Buffer.from(s, "base64"));

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
  // localhost (not 127.0.0.1) is a WebAuthn-allowed rpId over http.
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
    // Older CDP without `hasPrf`: ctap2_1 + hmac-secret still yields PRF.
    const { authenticatorId } = await client.send("WebAuthn.addVirtualAuthenticator", {
      options: base,
    });
    return authenticatorId;
  }
}

test("passkey custody: enroll → PRF-wrap → gated sign → hybrid envelope; fail-closed; seed-not-in-blob", async () => {
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

    assert.equal(await page.evaluate(() => window.__passkey.isAvailable()), true, "WebAuthn+PRF available");
    assert.equal(await page.evaluate(() => window.__passkey.label()), "Passkey", "label");

    // ── The wrap/sign LOGIC always holds (PRF-independent; the task's contingency).
    const turnB64 = await page.evaluate((m) => window.__passkey.buildTurn(m), MNEMONIC);
    assert.ok(turnB64 && turnB64.length > 0, "built a real normalized turn");
    const logic = await page.evaluate(
      ([m, t]) => window.__passkey.logicTest(m, t),
      [MNEMONIC, turnB64],
    );
    assert.equal(logic.seedInBlob, false, "LOGIC: mnemonic plaintext NOT in the wrapped blob");
    assert.equal(logic.wrongFailedClosed, true, "LOGIC: a wrong wrap secret fails closed (GCM)");
    assert.equal(logic.recoveredMatches, true, "LOGIC: the right secret recovers the exact mnemonic");
    assert.equal(logic.signer, logic.expectedPub, "LOGIC: envelope signer == mnemonic pubkey");
    assert.ok(logic.envLen > 64, "LOGIC: a non-trivial hybrid envelope was produced");

    // ── Enroll: PRF-gated wrap of the mnemonic under the virtual authenticator.
    let e2ePrf = true;
    let enrolled;
    try {
      enrolled = await page.evaluate((m) => window.__passkey.enroll(m), MNEMONIC);
    } catch (err) {
      if (/PRF/i.test(String(err))) {
        e2ePrf = false;
        console.warn("[passkey-test] PRF could not be virtualized here; asserted wrap/sign LOGIC only.");
      } else {
        throw err;
      }
    }

    if (e2ePrf) {
      // Custody bound the RIGHT dregg key.
      const rederived = await page.evaluate((m) => window.__passkey.rederivePub(m), MNEMONIC);
      assert.equal(enrolled.publicKey, rederived, "enrolled pubkey == mnemonic's re-derived pubkey");
      const cachedPub = await page.evaluate(() => window.__passkey.publicKey());
      assert.equal(cachedPub, rederived, "publicKey() (ungated) returns the bound identity");

      // seed-not-in-blob: the stored ciphertext holds no plaintext mnemonic.
      const blob = await page.evaluate(() => window.__passkey.storedBlob());
      assert.ok(blob, "an enrollment blob is stored");
      const ct = fromB64(blob.ct);
      const mnemonicBytes = new TextEncoder().encode(MNEMONIC);
      assert.equal(containsSub(ct, mnemonicBytes), false, "wrapped ciphertext contains NO plaintext mnemonic");
      // Not even the first few words leak.
      const firstWords = new TextEncoder().encode(MNEMONIC.split(" ").slice(0, 4).join(" "));
      assert.equal(containsSub(ct, firstWords), false, "no mnemonic-word run leaks into the blob");

      // ── Sign: gated PRF assertion → unwrap → HYBRID SignedTurn.
      const signed = await page.evaluate((t) => window.__passkey.signTurn(t), turnB64);
      assert.ok(signed.len > 64, "produced a non-trivial SignedTurn envelope");
      assert.equal(signed.signer, rederived, "envelope signer == the gated dregg key");
      assert.equal(signed.signerInEnvelope, true, "signer pubkey appears verbatim inside the envelope bytes");

      // ── FAIL-CLOSED: clear the authenticator's credential (wrong/failed auth).
      await client.send("WebAuthn.clearCredentials", { authenticatorId });
      const failed = await page.evaluate((t) => window.__passkey.signTurnExpectFail(t), turnB64);
      assert.equal(failed.failedClosed, true, "signTurn FAILS CLOSED when the authenticator can't assert");
      assert.match(failed.error, /refusing to sign|authentication/i, "fail-closed error is explicit");

      // ── The wrapped blob ALONE (no passkey) is still insufficient: it persists,
      //    but without a PRF assertion nothing can be unwrapped or signed.
      const stillStored = await page.evaluate(() => window.__passkey.storedBlob());
      assert.ok(stillStored && stillStored.ct === blob.ct, "ciphertext persists but cannot be used without the passkey");
    }

    assert.deepEqual(errors, [], `no page errors: ${errors.join("; ")}`);
    assert.ok(e2ePrf, "the virtual authenticator supported PRF (full enroll→sign e2e ran)");
  } finally {
    await browser.close();
    server.close();
  }
});
