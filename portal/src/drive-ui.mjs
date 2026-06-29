/**
 * The portal drive layer (browser). Connect an identity — the Cipherclerk
 * wallet (`window.dregg`) if installed, or an in-portal ephemeral identity for a
 * quick try — and fire REAL cap-gated turns against the edge node: publish a
 * minisite, open a metered lease, fire a transfer. Each shows the turn's
 * anti-blind-signing reading, the Ed25519 signature, the committed receipt, and
 * a link to verify the resulting cell trustlessly in-tab (the existing light
 * client at `cell.html`).
 *
 * Built on the published `@dregg/sdk/browser` — the portal is a real consumer.
 * The acting/signing/submitting path needs NO wasm (it is pure `fetch` + noble
 * Ed25519); the trustless verification on `cell.html` is the existing wasm light
 * client, unchanged.
 */

import { Identity, AgentRuntime, NodeClient } from "@dregg/sdk/browser";
import { fireTransfer, publishMinisite, openLease } from "./drive-actions.mjs";

const params = new URLSearchParams(location.search);
// Same convention as portal.js: ?api= override, else same-origin (Caddy proxies
// /api/* to the edge node).
const API = (params.get("api") || "").replace(/\/$/, "");
const NODE_BASE = API || location.origin;

const $ = (id) => document.getElementById(id);
function el(tag, attrs = {}, ...kids) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") e.className = v;
    else if (k === "html") e.innerHTML = v;
    else if (k.startsWith("on") && typeof v === "function") e.addEventListener(k.slice(2), v);
    else if (v != null) e.setAttribute(k, v);
  }
  for (const kid of kids) e.append(kid instanceof Node ? kid : document.createTextNode(String(kid)));
  return e;
}
const shortId = (s) => (s && s.length > 18 ? s.slice(0, 10) + "…" + s.slice(-6) : s);
const verifyHref = (cellHex) =>
  "./cell.html?id=" + encodeURIComponent(cellHex) + (API ? "&api=" + encodeURIComponent(API) : "");

// ── connection state ───────────────────────────────────────────────────────
let session = null; // { mode: "wallet"|"ephemeral", cellHex, runtime?, wallet? }

function setStatus(text, cls) {
  const s = $("drive-status");
  if (!s) return;
  s.className = "portal-status" + (cls ? " " + cls : "");
  s.textContent = text;
}

async function connectEphemeral() {
  setStatus("creating an in-portal identity…");
  try {
    const identity = Identity.generate();
    const runtime = new AgentRuntime(identity, NODE_BASE);
    // Materialize the cell on the node so it can pass turn authorization
    // (devnet faucet; on the live edge this may be gated — see the note).
    let faucetNote = "";
    try {
      await runtime.faucet(10000);
    } catch (e) {
      faucetNote = " (faucet unavailable here — actions will need a funded cell: " + (e.message || e) + ")";
    }
    session = { mode: "ephemeral", cellHex: identity.cellIdHex(), runtime };
    setStatus("connected · in-portal identity" + faucetNote, "live");
    renderConnected();
  } catch (e) {
    setStatus("could not create an identity: " + (e.message || e));
  }
}

async function connectWallet() {
  if (!window.dregg) {
    setStatus("Cipherclerk wallet not detected (window.dregg). Use the quick-try identity instead.");
    return;
  }
  setStatus("requesting authorization from the wallet…");
  try {
    // Authorization-first: the wallet mediates the connect (and shows a trusted
    // approval). We ask for the broad acting authority and read the balance.
    await window.dregg.authorize({ action: "connect", resource: "portal" });
    let bal;
    try { bal = (await window.dregg.queryBalance())?.balance; } catch { /* optional */ }
    session = { mode: "wallet", wallet: window.dregg, cellHex: null, balance: bal };
    setStatus("connected · Cipherclerk wallet", "live");
    renderConnected();
  } catch (e) {
    setStatus("wallet authorization refused: " + (e.message || e));
  }
}

function disconnect() {
  session = null;
  setStatus("not connected");
  renderConnectChoices();
}

// ── rendering ───────────────────────────────────────────────────────────────
function renderConnectChoices() {
  const root = $("drive-connect");
  root.replaceChildren();
  const hasWallet = !!window.dregg;
  root.append(
    el("div", { class: "portal-section-title" }, "connect an identity"),
    el("div", { class: "drive-connect-row" },
      el("button", { class: "deos-button", onclick: connectWallet, disabled: hasWallet ? null : "disabled", title: hasWallet ? "" : "no window.dregg provider found" },
        hasWallet ? "Connect Cipherclerk wallet" : "Cipherclerk wallet (not detected)"),
      el("button", { class: "deos-button", onclick: connectEphemeral }, "Quick try — in-portal identity"),
    ),
    el("p", { class: "portal-note" },
      "The wallet path is authorization-first: it mediates a trusted approval and signs with your key. " +
      "The quick-try path generates an ephemeral key in this tab and funds it from the devnet faucet — real turns, throwaway identity."),
  );
  $("drive-actions").replaceChildren();
  $("drive-cells").replaceChildren();
}

function renderConnected() {
  const root = $("drive-connect");
  root.replaceChildren();
  const idLine = session.cellHex
    ? el("span", { class: "portal-cell-id" }, shortId(session.cellHex))
    : el("span", { class: "deos-text" }, "wallet-held identity");
  root.append(
    el("div", { class: "portal-section-title" }, "connected — " + session.mode),
    el("div", { class: "deos-row", style: "justify-content:space-between;flex-wrap:wrap;gap:.5rem" },
      idLine,
      el("button", { class: "deos-toggle", onclick: disconnect }, "disconnect"),
    ),
    session.cellHex
      ? el("a", { class: "drive-link", href: verifyHref(session.cellHex), target: "_blank" }, "verify this cell trustlessly →")
      : el("span", { class: "deos-trust-detail" }, "balance: " + (session.balance ?? "—")),
  );
  renderActions();
  refreshCells();
}

function renderActions() {
  const root = $("drive-actions");
  root.replaceChildren();
  const wallet = session.mode === "wallet";

  // (c) fire a transfer
  const tTo = el("input", { class: "deos-input", placeholder: "recipient cell id (64 hex)", style: "flex:1;min-width:220px" });
  const tAmt = el("input", { class: "deos-input", type: "number", value: "10", min: "1", style: "width:90px" });
  root.append(actionCard("fire a transfer",
    "Move computrons to another cell — one conserving Effect::Transfer.",
    el("div", { class: "drive-form" }, tTo, tAmt,
      el("button", { class: "deos-button", onclick: () => runAction("transfer", { to: tTo.value, amount: tAmt.value }) }, "transfer")),
  ));

  // (a) publish a minisite
  const pName = el("input", { class: "deos-input", placeholder: "site name", style: "flex:1;min-width:160px" });
  const pBody = el("textarea", { class: "deos-input", placeholder: "<h1>hello</h1>  — your page body", rows: "4", style: "width:100%;resize:vertical" });
  root.append(actionCard("publish a minisite",
    "Commit your page's blake3 content hash into slot 0 of your cell (the dregg:// WebOfCells publish convention). Anyone can verify the cell holds exactly that commitment, trustlessly. Serving the matching bytes is the hosting layer.",
    el("div", { class: "drive-form", style: "flex-direction:column;align-items:stretch" }, pName, pBody,
      el("button", { class: "deos-button", style: "align-self:flex-start", onclick: () => runAction("publish", { name: pName.value, content: pBody.value }) }, "publish")),
    wallet ? "Publish uses the quick-try identity path (the wallet's signTurn covers transfers; richer turns ride signTurnV3 when the wallet exposes it)." : null,
  ));

  // (b) open a metered execution lease
  const lMax = el("input", { class: "deos-input", type: "number", value: "8", min: "1", style: "width:90px" });
  root.append(actionCard("open a metered execution lease",
    "Bind a capacity ceiling (maxSteps) to your cell and advance its durable checkpoint — a FieldLte∧Monotonic-gated SetField on slot 4. A run past the ceiling is refused by the executor.",
    el("div", { class: "drive-form" }, el("span", { class: "deos-text" }, "max steps"), lMax,
      el("button", { class: "deos-button", onclick: () => runAction("lease", { maxSteps: lMax.value }) }, "open + run")),
    wallet ? "Lease uses the quick-try identity path." : null,
  ));
}

function actionCard(title, desc, form, walletNote) {
  return el("div", { class: "deos-section" },
    el("div", { class: "deos-section-title" }, title),
    el("p", { class: "drive-desc" }, desc),
    walletNote ? el("p", { class: "portal-note" }, walletNote) : document.createComment(""),
    form,
    el("div", { class: "drive-result" }),
  );
}

async function runAction(kind, args) {
  const card = [...document.querySelectorAll(".deos-section")].find((s) =>
    s.querySelector(".deos-section-title")?.textContent?.startsWith(
      kind === "transfer" ? "fire a transfer" : kind === "publish" ? "publish" : "open a metered"));
  const out = card?.querySelector(".drive-result");
  if (out) out.replaceChildren(el("div", { class: "deos-trust pending" }, "building + signing + submitting the turn…"));

  // The wallet path covers transfers via the wallet's own signTurn; richer turns
  // ride the ephemeral runtime (the honest capability line).
  const needRuntime = session.mode !== "wallet" || kind !== "transfer";
  let runtime = session.runtime;
  if (needRuntime && !runtime) {
    // Spin up an ephemeral runtime on demand for a wallet user driving publish/lease.
    const identity = Identity.generate();
    runtime = new AgentRuntime(identity, NODE_BASE);
    try { await runtime.faucet(10000); } catch { /* surfaced on submit failure */ }
    session.aux = { cellHex: identity.cellIdHex() };
  }

  try {
    let res;
    if (kind === "transfer" && session.mode === "wallet") {
      const r = await session.wallet.signTurn({ action: "transfer", recipient: args.to, amount: Number(args.amount) });
      if (!r.submitted) throw new Error(r.error || "wallet did not submit");
      res = { walletTurn: r, kind: "transfer", verifyCellHex: args.to };
      renderWalletResult(out, res);
      return;
    }
    if (kind === "transfer") res = await fireTransfer(runtime, args.to, args.amount);
    else if (kind === "publish") res = await publishMinisite(runtime, args.name, args.content);
    else if (kind === "lease") res = await openLease(runtime, { maxSteps: Number(args.maxSteps) || 8 });
    renderResult(out, res);
    refreshCells();
  } catch (e) {
    if (out) out.replaceChildren(el("div", { class: "deos-trust refused" }, "refused: " + (e.message || e)));
  }
}

function row(label, value, mono) {
  return el("div", { class: "deos-row", style: "justify-content:space-between;gap:.5rem" },
    el("span", { class: "deos-text" }, label),
    el("span", { class: mono ? "portal-cell-id" : "deos-bind", style: "word-break:break-all;text-align:right" }, value));
}

function renderResult(out, res) {
  if (!out) return;
  const r = res.receipt;
  const kids = [
    el("div", { class: "deos-trust verified" }, "✓ committed — a real cap-gated turn"),
  ];
  if (res.explain) kids.push(el("div", { class: "drive-explain" }, res.explain));
  if (res.action?.authorization?.kind === "signature") kids.push(row("signature", "Ed25519 (signature present)"));
  if (res.kind === "publish") {
    kids.push(row("site cell", shortId(res.siteCellHex), true));
    kids.push(row("dregg uri", res.dreggUri, true));
    kids.push(row("content hash", shortId(res.contentHashHex), true));
  }
  if (res.kind === "lease") {
    kids.push(row("step", String(res.step)));
    kids.push(row("remaining", String(res.remaining)));
  }
  if (r) {
    kids.push(row("turn hash", shortId(r.turnHash), true));
    if (r.receiptHash) kids.push(row("receipt hash", shortId(r.receiptHash), true));
  }
  if (res.verifyCellHex) {
    kids.push(el("a", { class: "drive-link", href: verifyHref(res.verifyCellHex), target: "_blank" },
      "verify the resulting cell trustlessly →"));
  }
  out.replaceChildren(el("div", { class: "drive-result-inner" }, ...kids));
}

function renderWalletResult(out, res) {
  if (!out) return;
  out.replaceChildren(el("div", { class: "drive-result-inner" },
    el("div", { class: "deos-trust verified" }, "✓ submitted via the wallet"),
    res.walletTurn.turnId ? row("turn id", shortId(res.walletTurn.turnId), true) : document.createComment(""),
    res.verifyCellHex ? el("a", { class: "drive-link", href: verifyHref(res.verifyCellHex), target: "_blank" }, "verify the recipient cell →") : document.createComment(""),
  ));
}

// ── your cells ───────────────────────────────────────────────────────────────
async function refreshCells() {
  const root = $("drive-cells");
  if (!root) return;
  const cellHex = session?.cellHex || session?.aux?.cellHex;
  if (!cellHex) { root.replaceChildren(); return; }
  root.replaceChildren(el("div", { class: "portal-section-title" }, "your cells"),
    el("div", { class: "deos-trust-detail" }, "loading your cell from the edge…"));
  try {
    const node = new NodeClient(NODE_BASE);
    const c = await node.cell(cellHex);
    root.replaceChildren(
      el("div", { class: "portal-section-title" }, "your cells"),
      el("a", { class: "portal-cell", href: verifyHref(cellHex), target: "_blank" },
        el("span", { class: "portal-cell-id" }, shortId(cellHex)),
        el("span", { class: "portal-cell-row" }, "found ", el("b", {}, c.found ? "yes" : "no")),
        el("span", { class: "portal-cell-row" }, "balance ", el("b", {}, String(c.balance))),
        el("span", { class: "portal-cell-row" }, "nonce ", el("b", {}, String(c.nonce))),
        el("span", { class: "portal-cell-tags" }, el("span", { class: "portal-tag" }, "verify trustlessly →")),
      ),
    );
  } catch (e) {
    root.replaceChildren(el("div", { class: "portal-section-title" }, "your cells"),
      el("div", { class: "portal-err" }, "could not read your cell: " + (e.message || e)));
  }
}

// ── boot ─────────────────────────────────────────────────────────────────────
setStatus("not connected");
renderConnectChoices();
