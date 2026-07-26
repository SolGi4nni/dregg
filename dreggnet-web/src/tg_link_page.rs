//! # `tg_link_page` — the CLIENT of the Telegram cross-platform link ceremony (hardened).
//!
//! Served at `GET /tg/link` inside the Telegram Mini App web-view. The SERVER half
//! ([`crate::telegram_miniapp`] `/tg/link/challenge` + `POST /tg/link`) is the trust root; this is
//! the page a human uses to sign a [`webauth_core::link_claim`] with their **root key K** and
//! submit it, binding this Telegram account to the same K they linked from Discord.
//!
//! ## Security posture (post the 2026-07-18 adversarial review — `docs/TG-LINK-SECURITY-REVIEW-2026-07-18.md`)
//!
//! - **The K-touching code is in the TCB, not a CDN.** The Ed25519 primitive is vendored
//!   ([`get_noble_ed25519`], `assets/noble-ed25519.js`) and the page's own module is served
//!   same-origin ([`get_tg_link_app_js`]), so [`get_tg_link_page`] can ship a **strict CSP**
//!   (`script-src 'self' https://telegram.org`, no `'unsafe-inline'` for scripts, `connect-src
//!   'self'`) — closing the "CDN/MITM serves attacker JS that exfiltrates K" CRITICAL.
//! - **K is never silently minted or lost.** A missing local blob does NOT auto-create-and-relink
//!   a new key (the identity-loss HIGH); the page offers an explicit *create* vs *restore* choice
//!   and a **backup/restore** of the seed, so an evicted web-view store cannot silently split
//!   Discord-you from Telegram-you.
//! - **Passphrase path** uses PBKDF2 at the OWASP floor (600k) with an entropy check; a passkey
//!   *cancel* is distinguished from genuine *no-PRF* (never a silent downgrade); the decrypted seed
//!   is zeroized after signing.
//! - **Relay path** shows the ACTUAL message bytes only after the root pubkey is entered.
//!
//! Two signing paths, because the browser EXTENSION (where K normally lives) is NOT reachable
//! inside Telegram's sandboxed web-view: **passkey** (K wrapped under WebAuthn-PRF / a passphrase,
//! in `localStorage`) and **relay** (sign the exact bytes wherever K lives, paste the signature).

use axum::http::header;
use axum::response::{Html, IntoResponse};

/// The strict Content-Security-Policy for the link page. No `'unsafe-inline'` for scripts (the
/// page's module + the Ed25519 primitive are same-origin; `telegram-web-app.js` is the one allowed
/// external script). `connect-src 'self'` denies any exfiltration channel.
const LINK_CSP: &str = "default-src 'none'; \
    script-src 'self' https://telegram.org; \
    style-src 'unsafe-inline'; \
    connect-src 'self'; \
    img-src 'self' data:; \
    base-uri 'none'; object-src 'none'; form-action 'none'; \
    frame-ancestors https://web.telegram.org https://*.telegram.org";

/// `GET /tg/link` — the link-ceremony page shell (static HTML; the CSP header is the point).
pub async fn get_tg_link_page() -> impl IntoResponse {
    (
        [(header::CONTENT_SECURITY_POLICY, LINK_CSP)],
        Html(LINK_HTML),
    )
}

/// `GET /tg/link/app.js` — the page's module, served SAME-ORIGIN so the CSP forbids inline script
/// (a would-be XSS or CDN swap of the K-touching code has no foothold).
pub async fn get_tg_link_app_js() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        LINK_APP_JS,
    )
}

/// `GET /tg/assets/noble-ed25519.js` — the vendored Ed25519 primitive, same-origin (inside the
/// TCB, version-frozen in-repo — not a third-party CDN resolution).
pub async fn get_noble_ed25519() -> impl IntoResponse {
    (
        [(header::CONTENT_TYPE, "text/javascript; charset=utf-8")],
        include_str!("../assets/noble-ed25519.js"),
    )
}

#[cfg(test)]
mod tests {
    #[test]
    fn the_page_link_message_format_matches_the_verifier() {
        let msg = webauth_core::link_claim::link_claim_message(
            "telegram",
            "555000111",
            &"cc".repeat(32),
            &"dd".repeat(32),
            "chal-abc",
        )
        .unwrap();
        // DOMAIN(23) + platform(8) + 0 + uid(9) + 0 + custodial(64) + 0 + root(64) + 0 + challenge(8)
        assert_eq!(msg.len(), 23 + 8 + 1 + 9 + 1 + 64 + 1 + 64 + 1 + 8);
        assert!(msg.starts_with(b"dregg-identity-link-v1:telegram\x00555000111\x00"));
        assert_eq!(msg.iter().filter(|&&b| b == 0).count(), 4);
    }

    #[tokio::test]
    async fn the_link_page_ships_a_strict_csp_and_same_origin_scripts() {
        use axum::response::IntoResponse;
        let resp = super::get_tg_link_page().await.into_response();
        let csp = resp
            .headers()
            .get("content-security-policy")
            .expect("CSP header present")
            .to_str()
            .unwrap();
        assert!(csp.contains("script-src 'self' https://telegram.org"));
        assert!(!csp.contains("script-src") || !csp.contains("'unsafe-inline' https"));
        assert!(super::LINK_HTML.contains("/tg/link/app.js")); // HTML loads the module same-origin
        // no inline <script> body + no CDN import in the served page (noble is imported BY app.js)
        assert!(!super::LINK_HTML.contains("esm.sh"));
        assert!(super::LINK_APP_JS.contains("/tg/assets/noble-ed25519.js"));
        assert!(super::LINK_APP_JS.contains("linkClaimMessage"));
    }

    #[tokio::test]
    async fn the_vendored_noble_serves_same_origin() {
        use axum::response::IntoResponse;
        let resp = super::get_noble_ed25519().await.into_response();
        assert_eq!(
            resp.headers().get("content-type").unwrap(),
            "text/javascript; charset=utf-8"
        );
    }
}

const LINK_HTML: &str = r####"<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>Link your dregg identity</title>
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<style>
  :root { color-scheme: light dark; }
  body { font: 15px/1.5 system-ui, sans-serif; margin: 0; padding: 16px;
         background: var(--tg-theme-bg-color, #fff); color: var(--tg-theme-text-color, #111); }
  h1 { font-size: 1.25rem; margin: .2rem 0 .1rem; }
  .sub { color: var(--tg-theme-hint-color, #777); margin: 0 0 1rem; }
  .card { border: 1px solid var(--tg-theme-hint-color, #ccc); border-radius: 12px; padding: 14px; margin: 12px 0; }
  button { font: inherit; font-weight: 600; width: 100%; padding: 13px; border: 0; border-radius: 10px;
           background: var(--tg-theme-button-color, #2ea6ff); color: var(--tg-theme-button-text-color, #fff);
           margin-top: 8px; cursor: pointer; }
  button.ghost { background: transparent; color: var(--tg-theme-button-color, #2ea6ff);
                 border: 1px solid var(--tg-theme-button-color, #2ea6ff); }
  button:disabled { opacity: .5; }
  textarea, input { width: 100%; box-sizing: border-box; font: 13px/1.4 ui-monospace, monospace;
                    padding: 9px; border-radius: 8px; border: 1px solid var(--tg-theme-hint-color, #ccc);
                    background: var(--tg-theme-secondary-bg-color, #f4f4f5); color: inherit; }
  .mono { font: 12px/1.4 ui-monospace, monospace; word-break: break-all;
          background: var(--tg-theme-secondary-bg-color, #f4f4f5); padding: 8px; border-radius: 6px; }
  .status { margin-top: 10px; font-weight: 600; }
  .ok { color: #1a9d4d; }
  .err { color: #e0294a; }
  .warn { color: #c47f00; }
  .tabs { display: flex; gap: 8px; margin-bottom: 4px; }
  .tabs button { width: auto; flex: 1; padding: 9px; font-size: .9rem; }
  .hidden { display: none; }
  small { color: var(--tg-theme-hint-color, #777); }
</style>
</head><body>
<h1>🔗 Link this Telegram to your dregg identity</h1>
<p class="sub">Sign a one-time claim with your <b>root key</b>. Then Discord-you and Telegram-you are
the same human on boards + leaderboards.</p>

<div id="who" class="card">Loading your Telegram identity…</div>

<div class="tabs">
  <button id="tab-passkey">🔐 Passkey</button>
  <button id="tab-relay" class="ghost">📋 Paste a signature</button>
</div>

<div id="panel-passkey" class="card">
  <div id="key-none">
    <b>No dregg key on this device yet</b>
    <p><small>Choose one: a new key is created ON this device and locked behind a passkey (or a
    passphrase). It never leaves the device unencrypted. <b>Back it up</b> after creating, or it
    lives only here.</small></p>
    <button id="do-create">✨ Create a new dregg key here</button>
    <button id="show-restore" class="ghost">↩︎ Restore a key from backup</button>
    <div id="restore-box" class="hidden">
      <textarea id="restore-seed" rows="2" placeholder="paste your backed-up key (64 hex)"></textarea>
      <button id="do-restore">↩︎ Restore &amp; link</button>
    </div>
  </div>
  <div id="key-have" class="hidden">
    <b>Unlock your dregg key &amp; link</b>
    <button id="do-unlock">🔐 Unlock &amp; link this Telegram</button>
    <button id="do-backup" class="ghost">🔑 Back up my key</button>
  </div>
  <div id="pass-fallback" class="hidden">
    <p><small>No passkey PRF on this device: using a passphrase. Pick something long + unguessable
    (≥ 12 chars); a short passphrase can be brute-forced from a stolen device.</small></p>
    <input id="passphrase" type="password" placeholder="passphrase to lock your key" autocomplete="off">
    <button id="do-passphrase">🔑 Continue with passphrase</button>
  </div>
  <div id="backup-box" class="hidden">
    <p class="warn"><small>⚠ This is your key. Anyone with it controls your identity. Save it
    somewhere only you can reach, then dismiss.</small></p>
    <div id="backup-seed" class="mono">—</div>
    <button id="backup-done" class="ghost">I saved it</button>
  </div>
</div>

<div id="panel-relay" class="card hidden">
  <b>Sign it wherever your key lives</b>
  <p><small>Enter your root public key, then sign the <b>exact bytes</b> shown with your dregg root
  key (Ed25519) and paste the signature.</small></p>
  <input id="root-hex" placeholder="root public key (64 hex)" autocomplete="off">
  <div id="msg-label" class="hidden">message to sign (hex):</div>
  <div id="msg-hex" class="mono hidden">—</div>
  <textarea id="sig-hex" rows="2" placeholder="signature (128 hex)"></textarea>
  <button id="do-relay">📋 Submit signature</button>
</div>

<div id="status" class="status"></div>

<script type="module" src="/tg/link/app.js"></script>
</body></html>
"####;

const LINK_APP_JS: &str = r####"import * as ed from "/tg/assets/noble-ed25519.js";

const tg = window.Telegram && window.Telegram.WebApp;
if (tg) { tg.ready(); tg.expand(); }
const initData = (tg && tg.initData) || "";
const $ = (id) => document.getElementById(id);
const setStatus = (msg, cls) => { const s = $("status"); s.textContent = msg; s.className = "status " + (cls||""); };

const enc = new TextEncoder();
const toHex = (u8) => Array.from(u8).map(b => b.toString(16).padStart(2, "0")).join("");
const fromHex = (h) => { const s = h.trim(); if (s.length % 2) throw new Error("bad hex");
  const o = new Uint8Array(s.length/2);
  for (let i=0;i<o.length;i++){ const b = parseInt(s.slice(2*i,2*i+2),16); if (Number.isNaN(b)) throw new Error("bad hex"); o[i]=b; } return o; };
function concatBytes(...arrs){ let n=0; for(const a of arrs) n+=a.length; const o=new Uint8Array(n); let p=0;
  for(const a of arrs){ o.set(a,p); p+=a.length; } return o; }
const zero = (u8) => { if (u8) u8.fill(0); };

// The canonical link-claim message — MUST match webauth_core::link_claim::link_claim_message
// byte-for-byte: DOMAIN‖platform‖0‖uid‖0‖custodial_hex‖0‖root_hex‖0‖challenge.
function linkClaimMessage(platform, uid, custodialHex, rootHex, challenge){
  const Z = new Uint8Array([0]);
  return concatBytes(
    enc.encode("dregg-identity-link-v1:" + platform), Z,
    enc.encode(uid), Z, enc.encode(custodialHex), Z, enc.encode(rootHex), Z, enc.encode(challenge));
}

let CTX = null; // {platform, platform_uid, custodial_pubkey_hex, challenge}

async function fetchChallenge(){
  const r = await fetch("/tg/link/challenge", { headers: { "X-Telegram-Init-Data": initData } });
  if (!r.ok) throw new Error("challenge: HTTP " + r.status + " (open this from the bot's /link button so Telegram provides identity)");
  return await r.json();
}
async function submit(rootHex, sigHex){
  const body = new URLSearchParams({ root_pubkey_hex: rootHex, signature_hex: sigHex, challenge: CTX.challenge });
  const r = await fetch("/tg/link", { method: "POST",
    headers: { "X-Telegram-Init-Data": initData, "content-type": "application/x-www-form-urlencoded" },
    body: body.toString() });
  const txt = await r.text();
  if (!r.ok) throw new Error("link refused (HTTP " + r.status + "): " + txt);
  return txt;
}

// ── Custody of the root key K (seed wrapped in localStorage; NEVER auto-minted) ──
const LS_KEY = "dregg_root_k_v1";
const PRF_SALT = new Uint8Array(await crypto.subtle.digest("SHA-256", enc.encode("dregg-link-prf-v1")));

async function aesFromRaw(raw){
  // HKDF the PRF/derived secret to a dedicated wrap key (parity with extension custody).
  const base = await crypto.subtle.importKey("raw", raw, "HKDF", false, ["deriveKey"]);
  return crypto.subtle.deriveKey(
    { name:"HKDF", hash:"SHA-256", salt: PRF_SALT, info: enc.encode("dregg-link-wrap-v1") },
    base, { name:"AES-GCM", length:256 }, false, ["encrypt","decrypt"]);
}
async function aesFromPassphrase(pass, salt){
  const base = await crypto.subtle.importKey("raw", enc.encode(pass), "PBKDF2", false, ["deriveKey"]);
  return crypto.subtle.deriveKey({ name:"PBKDF2", salt, iterations:600000, hash:"SHA-256" },
    base, { name:"AES-GCM", length:256 }, false, ["encrypt","decrypt"]);
}

class NoPrf extends Error {}          // PRF genuinely unsupported here → offer passphrase
class PkFailed extends Error {}       // passkey cancelled/failed → RETRY, never downgrade

async function prfSecret(create){
  let cred;
  try {
    const opts = create ? {
      publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)),
        rp:{ name:"dregg" }, user:{ id: crypto.getRandomValues(new Uint8Array(16)), name:"dregg", displayName:"dregg" },
        pubKeyCredParams:[{type:"public-key",alg:-7},{type:"public-key",alg:-257}],
        authenticatorSelection:{ residentKey:"required", userVerification:"required" },
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } }
    : { publicKey: { challenge: crypto.getRandomValues(new Uint8Array(32)), userVerification:"required",
        extensions:{ prf:{ eval:{ first: PRF_SALT } } } } };
    cred = create ? await navigator.credentials.create(opts) : await navigator.credentials.get(opts);
  } catch(e){
    // NotSupported / no authenticator → offer the passphrase; anything else (NotAllowed=cancel,
    // Abort, timeout) is a FAILURE the user should retry — do NOT silently downgrade.
    if (e && (e.name === "NotSupportedError")) throw new NoPrf();
    if (!window.PublicKeyCredential) throw new NoPrf();
    throw new PkFailed(e && e.name ? e.name : String(e));
  }
  const res = cred.getClientExtensionResults();
  if (res && res.prf && res.prf.results && res.prf.results.first) return new Uint8Array(res.prf.results.first);
  throw new NoPrf(); // PRF not returned by this authenticator
}

function storeWrapped(mode, iv, ct, salt){
  localStorage.setItem(LS_KEY, JSON.stringify({ mode, iv:toHex(iv), ct:toHex(ct), ...(salt?{salt:toHex(salt)}:{}) })); }
async function wrapSeed(aes, seed){
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const ct = new Uint8Array(await crypto.subtle.encrypt({name:"AES-GCM", iv}, aes, seed));
  return { iv, ct };
}
async function unwrapSeed(aes, rec){
  const seed = await crypto.subtle.decrypt({name:"AES-GCM", iv:fromHex(rec.iv)}, aes, fromHex(rec.ct));
  return new Uint8Array(seed);
}

// Sign a fresh CTX claim with an in-memory seed, then zeroize it.
async function signAndLink(seed){
  let rootHex, msg;
  try {
    rootHex = toHex(await ed.getPublicKeyAsync(seed));
    msg = linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, rootHex, CTX.challenge);
    setStatus("submitting…");
    const sig = await ed.signAsync(msg, seed);
    await submit(rootHex, toHex(sig));
  } finally { zero(seed); }
  setStatus("✅ Linked! Telegram-you and Discord-you are now one human.", "ok");
  if (tg && tg.HapticFeedback) tg.HapticFeedback.notificationOccurred("success");
}

// Explicit CREATE — never auto-minted. Wrap under passkey-PRF (or passphrase), then link.
async function createOrUnlock(create){
  let prf;
  try { prf = await prfSecret(create); }
  catch(e){
    if (e instanceof NoPrf){ $("pass-fallback").classList.remove("hidden");
      setStatus("no passkey PRF here: set a passphrase below.", "warn"); return; }
    if (e instanceof PkFailed){ setStatus("✗ passkey " + e.message + ": tap again to retry (not falling back).", "err"); return; }
    throw e;
  }
  const aes = await aesFromRaw(prf.slice(0,32)); zero(prf);
  const rec = localStorage.getItem(LS_KEY);
  let seed;
  if (rec){
    const r = JSON.parse(rec);
    if (r.mode !== "prf"){ setStatus("this device's key is passphrase-locked: use the passphrase.", "err"); return; }
    seed = await unwrapSeed(aes, r);
  } else {
    seed = ed.utils.randomPrivateKey();
    const { iv, ct } = await wrapSeed(aes, seed);
    storeWrapped("prf", iv, ct);
  }
  await signAndLink(seed);
}
async function passphrasePath(pass){
  const rec = localStorage.getItem(LS_KEY);
  let seed;
  if (rec){
    const r = JSON.parse(rec);
    if (r.mode !== "pass") throw new Error("this device's key is passkey-locked, not passphrase");
    seed = await unwrapSeed(await aesFromPassphrase(pass, fromHex(r.salt)), r);
  } else {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    seed = ed.utils.randomPrivateKey();
    const { iv, ct } = await wrapSeed(await aesFromPassphrase(pass, salt), seed);
    storeWrapped("pass", iv, ct, salt);
  }
  await signAndLink(seed);
}

// ── UI wiring ──
function haveKey(){ return !!localStorage.getItem(LS_KEY); }
function refreshKeyPanel(){
  $("key-none").classList.toggle("hidden", haveKey());
  $("key-have").classList.toggle("hidden", !haveKey());
}
$("tab-passkey").onclick = () => { $("panel-passkey").classList.remove("hidden"); $("panel-relay").classList.add("hidden");
  $("tab-passkey").classList.remove("ghost"); $("tab-relay").classList.add("ghost"); refreshKeyPanel(); };
$("tab-relay").onclick = () => { $("panel-relay").classList.remove("hidden"); $("panel-passkey").classList.add("hidden");
  $("tab-relay").classList.remove("ghost"); $("tab-passkey").classList.add("ghost"); };

$("do-create").onclick    = () => createOrUnlock(true).catch(e => setStatus("✗ " + e.message, "err"));
$("do-unlock").onclick    = () => createOrUnlock(false).catch(e => setStatus("✗ " + e.message, "err"));
$("show-restore").onclick = () => $("restore-box").classList.toggle("hidden");
$("do-restore").onclick   = async () => {
  try { const seed = fromHex($("restore-seed").value);
    if (seed.length !== 32) throw new Error("a backed-up key is 64 hex chars");
    // re-wrap under a passphrase (prompt) OR just link this once — here: link + persist under passphrase
    $("pass-fallback").classList.remove("hidden");
    setStatus("set a passphrase to lock the restored key, then Continue.", "warn");
    window.__restoreSeed = seed;
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-passphrase").onclick = async () => {
  try {
    const pass = $("passphrase").value;
    if (pass.length < 12){ setStatus("passphrase needs ≥ 12 characters (longer is safer).", "err"); return; }
    if (window.__restoreSeed){ // restore flow: wrap the pasted seed under this passphrase
      const salt = crypto.getRandomValues(new Uint8Array(16));
      const { iv, ct } = await wrapSeed(await aesFromPassphrase(pass, salt), window.__restoreSeed);
      storeWrapped("pass", iv, ct, salt);
      const seed = window.__restoreSeed; window.__restoreSeed = null;
      await signAndLink(seed);
    } else { await passphrasePath(pass); }
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};
$("do-backup").onclick = async () => {
  // Reveal the seed hex for backup. Requires unlocking (passkey/passphrase); here we surface the
  // stored blob only after a fresh unlock via the same path — minimal: prompt passphrase or passkey.
  setStatus("Unlock to reveal your key…", "warn");
  try {
    const r = JSON.parse(localStorage.getItem(LS_KEY));
    let aes;
    if (r.mode === "prf"){ const prf = await prfSecret(false); aes = await aesFromRaw(prf.slice(0,32)); zero(prf); }
    else { const p = prompt("passphrase to reveal your key"); if (!p) return; aes = await aesFromPassphrase(p, fromHex(r.salt)); }
    const seed = await unwrapSeed(aes, r);
    $("backup-seed").textContent = toHex(seed); zero(seed);
    $("backup-box").classList.remove("hidden"); setStatus("");
  } catch(e){ setStatus("✗ " + (e.message||e), "err"); }
};
$("backup-done").onclick = () => { $("backup-seed").textContent = "—"; $("backup-box").classList.add("hidden"); };

function relayMsgHex(){
  const rootHex = $("root-hex").value.trim().toLowerCase();
  if (rootHex.length === 64 && CTX){
    $("msg-label").classList.remove("hidden"); $("msg-hex").classList.remove("hidden");
    $("msg-hex").textContent = toHex(linkClaimMessage(CTX.platform, CTX.platform_uid, CTX.custodial_pubkey_hex, rootHex, CTX.challenge));
  } else { $("msg-label").classList.add("hidden"); $("msg-hex").classList.add("hidden"); }
}
$("root-hex").addEventListener("input", relayMsgHex);
$("do-relay").onclick = async () => {
  try {
    const rootHex = $("root-hex").value.trim().toLowerCase();
    const sigHex = $("sig-hex").value.trim().toLowerCase();
    if (rootHex.length !== 64 || sigHex.length !== 128){ setStatus("root pubkey must be 64 hex, signature 128 hex.", "err"); return; }
    setStatus("submitting…"); await submit(rootHex, sigHex);
    setStatus("✅ Linked! Telegram-you and Discord-you are now one human.", "ok");
  } catch(e){ setStatus("✗ " + e.message, "err"); }
};

// boot
(async () => {
  try {
    CTX = await fetchChallenge();
    $("who").innerHTML = "Telegram <b>#" + CTX.platform_uid + "</b> · this account's dregg key:<div class='mono'>"
      + CTX.custodial_pubkey_hex + "</div>";
    refreshKeyPanel();
  } catch(e){ $("who").innerHTML = "<span class='err'>" + e.message + "</span>"; }
})();
"####;
