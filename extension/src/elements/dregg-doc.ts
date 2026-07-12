/**
 * `<dregg-doc src="dregg://doc/…">` — THE VERIFIABLE DOCUMENT SURFACE (the
 * culminating authoring path: a person authors a verifiable document a STRANGER
 * can check). DREGG-DOCUMENT-FOUNDATION.md, wasm/src/bindings_doc.rs
 * (`DocCollabWorld`).
 *
 * It renders a document's current reading; and when the document carries a
 * first-class CONFLICT — two authors edited concurrently — it renders the engine's
 * ConflictView: BOTH live alternatives, side by side, attributed to who wrote
 * them, NEVER hiding one. A click on a resolution affordance picks an alternative
 * and PUBLISHES the resolved document as a real cap-gated verified turn whose
 * receipt commits the resealed umem `heap_root` — routed, like the poll's cast,
 * through the un-overlayable confirm-intent consent BEFORE any commit.
 *
 * It is a THIN VIEW, exactly like `<dregg-poll>` / `<dregg-embed>`: a **closed**
 * shadow root (the page cannot read or rewrite the render), NO wasm, NO keys, NO
 * doc graph — every fact comes back tiered through the port from the background
 * `DocEngine`. It REUSES `DreggElement` (closed shadow, trust reflection, fail-
 * closed) but overrides the boot flow to speak the document port. An unverifiable
 * document renders NOTHING (fallback link + warning).
 */

import { DreggElement } from "./dregg-poll";
import type {
  DocPort,
  DocPortRequest,
  DocPortResponse,
  DocResolveResponse,
  DocRenderResponse,
  DocConflictResponse,
  DocPublishResponse,
  DocVerifyResponse,
  DocTextPort,
  DocTextPortRequest,
  DocTextPortResponse,
  DocTextResolveResponse,
  DocTextRenderResponse,
  DocTextEditResponse,
  DocTextPublishResponse,
  DocTextVerifyResponse,
  TrustTier,
} from "../port";

/** The port factory the element uses to reach the engine. Overridable for tests
 *  (the fixture routes it in-page to a real `DocEngine` over a wasm `DocCollabWorld`). */
export type DocPortFactory = () => DocPort;
let docPortFactory: DocPortFactory | null = null;
export function setDocPortFactory(f: DocPortFactory): void {
  docPortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background
 *  DocEngine. The router wraps handler results as `{ id, result }` | `{ error }`. */
function chromeMessagePort(): DocPort {
  return {
    async request(req: DocPortRequest): Promise<DocPortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:doc", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as DocPortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, tier: "none", verified: false, error: String((resp as { error: unknown }).error) } as DocPortResponse;
      }
      return resp as DocPortResponse;
    },
  };
}

function getDocPort(): DocPort {
  return (docPortFactory ?? chromeMessagePort)();
}

/** The port factory the EDITABLE element uses to reach the free-text engine.
 *  Overridable for tests (the fixture routes it in-page to a real `DocTextEngine`
 *  over a wasm `DocTextWorld`). */
export type DocTextPortFactory = () => DocTextPort;
let docTextPortFactory: DocTextPortFactory | null = null;
export function setDocTextPortFactory(f: DocTextPortFactory): void {
  docTextPortFactory = f;
}

/** The default transport: a `chrome.runtime` message hop to the background
 *  DocTextEngine (a distinct channel from the conflict-flow DocEngine). */
function chromeMessageTextPort(): DocTextPort {
  return {
    async request(req: DocTextPortRequest): Promise<DocTextPortResponse> {
      const resp = await chrome.runtime.sendMessage({ type: "dregg:doctext", ...req });
      if (resp && typeof resp === "object" && "result" in resp) {
        return (resp as { result: unknown }).result as DocTextPortResponse;
      }
      if (resp && typeof resp === "object" && "error" in resp) {
        return { ok: false, tier: "none", verified: false, error: String((resp as { error: unknown }).error) } as DocTextPortResponse;
      }
      return resp as DocTextPortResponse;
    },
  };
}

function getDocTextPort(): DocTextPort {
  return (docTextPortFactory ?? chromeMessageTextPort)();
}

const BADGE: Record<TrustTier, string> = {
  extension: "✓ verified by your cipherclerk",
  sdk: "✓ verified in this page",
  server: "✓ verified by dregg.net (trust the origin)",
  none: "⚠ unverified — original link shown",
};

const STYLE = `
:host { display: block; font-family: system-ui, sans-serif; }
.wrap { border: 1px solid #7c6cf0; border-radius: 10px; padding: 12px 14px; background: #faf9ff; color: #1c1830; }
.title { font-weight: 600; font-size: 13px; margin-bottom: 8px; color: #4030a0; }
.doc { font-size: 14px; line-height: 1.5; }
.doc .deos-vstack { display: flex; flex-direction: column; gap: 6px; }
.doc .deos-row { display: flex; flex-wrap: wrap; gap: 12px; }
.doc .deos-row > * { flex: 1 1 0; min-width: 160px; border: 1px solid #cdbff2; border-radius: 8px; padding: 8px 10px; background: #fff; }
.doc .deos-button { font: inherit; font-size: 12px; padding: 4px 10px; border: 1px solid #7c6cf0; border-radius: 6px; background: #fff; color: #4030a0; cursor: pointer; text-align: left; }
.doc .deos-button:hover { background: #7c6cf0; color: #fff; }
.note { font-size: 12px; color: #b02a37; margin-top: 8px; }
.note:empty { display: none; }
.badge { font-size: 11px; margin-top: 10px; color: #2f7d32; }
.badge.none { color: #b02a37; }
:host([conflict]) .wrap { border-color: #d98a00; }
:host([conflict]) .title::after { content: " — ⚠ conflict (both alternatives shown)"; color: #8a5a00; font-weight: 400; }
.doc-edit { font-size: 14px; line-height: 1.55; border: 1px solid #cdbff2; border-radius: 8px; padding: 8px 10px; background: #fff; min-height: 2.4em; white-space: pre-wrap; outline: none; }
.doc-edit:focus { border-color: #7c6cf0; box-shadow: 0 0 0 2px #e7e2fb; }
.patchinfo { font-size: 11px; color: #4030a0; margin-top: 6px; }
.patchinfo:empty { display: none; }
.controls { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 8px; }
.controls button { font: inherit; font-size: 12px; padding: 4px 10px; border: 1px solid #7c6cf0; border-radius: 6px; background: #fff; color: #4030a0; cursor: pointer; }
.controls button:hover { background: #7c6cf0; color: #fff; }
.controls button:disabled { opacity: .5; cursor: default; }
:host([dirty]) .title::after { content: " — ✎ unpublished edits (publish to commit a verified turn)"; color: #8a5a00; font-weight: 400; }
`;

/** `<dregg-doc>` — a verifiable, authorable document surface. */
export class DreggDoc extends DreggElement {
  private doc: DocPort = getDocPort();
  private text: DocTextPort = getDocTextPort();
  private uri = "";
  private wired = false;
  private editableWired = false;

  /** Override the poll boot: resolve the document → render (ConflictView or clean). */
  protected async boot(): Promise<void> {
    this.booted = true;
    const uri = this.src;
    if (!uri) return this.failClosed("no source");
    this.uri = uri;

    // `<dregg-doc editable>` — the FREE-TEXT authoring path (a distinct port +
    // engine over `DocTextWorld`); it never touches the conflict-flow path below.
    if (this.hasAttribute("editable")) return this.bootEditable();

    let resolved: DocResolveResponse;
    try {
      resolved = (await this.doc.request({ op: "resolveDoc", uri })) as DocResolveResponse;
    } catch (e) {
      return this.failClosed(String((e as Error)?.message ?? e));
    }
    if (!resolved || !resolved.ok || !resolved.verified) {
      return this.failClosed(resolved?.error || "could not verify");
    }
    await this.paintInitial(resolved);
  }

  /** Abstract on the base (poll flow); the doc overrides boot(). */
  protected async renderVerified(): Promise<void> {
    /* unused — the doc overrides boot() and speaks the document port. */
  }

  /** Build the shell, wire the (single, delegated) click handler on the closed
   *  root, and inject the engine-authored document/ConflictView HTML. */
  private async paintInitial(resolved: DocResolveResponse): Promise<void> {
    const render = (await this.doc.request({ op: "renderDoc", uri: this.uri })) as DocRenderResponse;
    if (!render.ok || !render.html) return this.failClosed(render.error || "render failed");

    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    wrap.innerHTML =
      `<div class="title">Document — ${escapeHtml(resolved.object?.addr || "")}</div>` +
      `<div class="doc"></div>` +
      `<div class="note" aria-live="polite"></div>` +
      `<div class="badge"></div>`;
    root.replaceChildren(style, wrap);

    this.injectDoc(root, render);

    // The click wire is bound to the CLOSED root — the page cannot inject
    // affordances; only the engine's rendered `.deos-button`s carry a turn.
    if (!this.wired) {
      root.addEventListener("click", (ev) => void this.onShadowClick(ev));
      this.wired = true;
    }

    this.reflectTrust("extension", true);
    this.setAttribute("receipts", String(resolved.receiptCount ?? 0));
    if (resolved.commitment) this.setAttribute("commitment", resolved.commitment);
    this.paintBadge(root, "extension", true);

    exposeRootForTest(this, root);
  }

  private async onShadowClick(ev: Event): Promise<void> {
    const target = ev.target as HTMLElement | null;
    const btn = target?.closest?.(".deos-button, button[data-turn]") as HTMLElement | null;
    if (!btn) return;
    const turn = btn.getAttribute("data-turn");
    if (!turn) return;
    const arg = Number(btn.getAttribute("data-arg") || "0");
    const root = this.closedShadow();
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    setDisabled(root, true);

    try {
      if (turn === "stitch") {
        await this.doc.request({ op: "stitch", uri: this.uri });
      } else if (turn === "resolve") {
        // Pick the alternative (STAGE) — the conflict is still shown until publish.
        const staged = (await this.doc.request({ op: "resolveConflict", uri: this.uri, choice: arg })) as DocConflictResponse;
        if (!staged.ok) {
          note.textContent = `⚠ ${staged.error || "could not pick"}`;
          setDisabled(root, false);
          return;
        }
        // The publish routes through consent (the faithful reading) BEFORE committing.
        const pub = (await this.doc.request({ op: "publish", uri: this.uri })) as DocPublishResponse;
        if (pub.refused) {
          note.textContent = `⚠ publish refused: ${pub.reason || "refused"}`;
          this.setAttribute("publish-refused", "");
        } else if (pub.ok) {
          this.removeAttribute("publish-refused");
          this.setAttribute("receipts", String(pub.receiptCount ?? 0));
          if (pub.commitment) this.setAttribute("commitment", pub.commitment);
          if (pub.substrateMatches) this.setAttribute("substrate-matches", "");
          else this.removeAttribute("substrate-matches");
        }
      } else {
        note.textContent = `⚠ unknown affordance: ${turn}`;
      }
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      setDisabled(root, false);
      return;
    }

    await this.repaint(root);
    setDisabled(root, false);
  }

  /** Re-render from the engine (never from the page) + re-verify the badge. The
   *  tree SHAPE changes across a publish (ConflictView collapses to the clean
   *  document), so we replace the whole `.doc` fragment. */
  private async repaint(root: ShadowRoot): Promise<void> {
    const render = (await this.doc.request({ op: "renderDoc", uri: this.uri })) as DocRenderResponse;
    if (render.ok && render.html) this.injectDoc(root, render);

    const verify = (await this.doc.request({ op: "verify", uri: this.uri })) as DocVerifyResponse;
    this.reflectTrust(verify.tier, verify.verified);
    if (!verify.verified) {
      this.removeAttribute("verified");
      this.setAttribute("error", "");
    }
    if (verify.commitment) this.setAttribute("commitment", verify.commitment);
    if (typeof verify.receiptCount === "number") this.setAttribute("receipts", String(verify.receiptCount));
    this.paintBadge(root, verify.tier, verify.verified);
  }

  /** Inject the engine-authored HTML (the ConflictView holds BOTH alternatives —
   *  never hidden) and reflect the conflict state. */
  private injectDoc(root: ShadowRoot, render: DocRenderResponse): void {
    const doc = root.querySelector(".doc") as HTMLElement;
    // Engine-authored HTML (from the extension wasm, not the page) — safe to inject.
    doc.innerHTML = render.html ?? "";
    if (render.hasConflict) {
      this.setAttribute("conflict", "");
      this.setAttribute("alternatives", String(render.alternatives?.length ?? 0));
    } else {
      this.removeAttribute("conflict");
      this.removeAttribute("alternatives");
    }
  }

  private paintBadge(root: ShadowRoot, tier: TrustTier, verified: boolean): void {
    const badge = root.querySelector(".badge") as HTMLElement;
    if (!badge) return;
    const shown: TrustTier = verified ? tier : "none";
    badge.textContent = BADGE[shown];
    badge.classList.toggle("none", shown === "none");
  }

  // ── FREE-TEXT AUTHORING (`<dregg-doc editable>`) ─────────────────────────────
  // A person types PROSE into a contenteditable inside the CLOSED shadow; each
  // input diffs into the MINIMAL patch (engine-side, over `DocTextWorld`) and the
  // view repaints from the engine's canonical text PRESERVING the caret (the keyed
  // reconciler). A publish affordance commits the accumulated edits as a real
  // cap-gated verified turn, routed through consent. FAIL-CLOSED: an unverifiable
  // doc-cell renders NO editable region.

  /** Resolve the free-text doc-cell → the editable render, or fail closed. */
  private async bootEditable(): Promise<void> {
    let resolved: DocTextResolveResponse;
    try {
      resolved = (await this.text.request({ op: "resolveText", uri: this.uri })) as DocTextResolveResponse;
    } catch (e) {
      return this.failClosed(String((e as Error)?.message ?? e));
    }
    if (!resolved || !resolved.ok || !resolved.verified) {
      return this.failClosed(resolved?.error || "could not verify");
    }
    await this.paintEditable(resolved);
  }

  /** Build the editable shell: a contenteditable prose region + a publish
   *  affordance, both inside the CLOSED root (the page cannot inject either). */
  private async paintEditable(resolved: DocTextResolveResponse): Promise<void> {
    const render = (await this.text.request({ op: "renderText", uri: this.uri })) as DocTextRenderResponse;
    if (!render.ok) return this.failClosed(render.error || "render failed");

    const root = this.closedShadow();
    const style = document.createElement("style");
    style.textContent = STYLE;
    const wrap = document.createElement("div");
    wrap.className = "wrap";
    wrap.innerHTML =
      `<div class="title">Document — ${escapeHtml(resolved.object?.addr || "")} (editable)</div>` +
      `<div class="doc-edit" contenteditable="true" spellcheck="false" role="textbox" aria-multiline="true" aria-label="editable document"></div>` +
      `<div class="patchinfo" aria-live="polite"></div>` +
      `<div class="controls"><button type="button" data-turn="publish-text">Publish edits (verified turn)</button></div>` +
      `<div class="note" aria-live="polite"></div>` +
      `<div class="badge"></div>`;
    root.replaceChildren(style, wrap);

    // Seed the prose from the engine's text (NEVER from the page).
    const editable = wrap.querySelector(".doc-edit") as HTMLElement;
    editable.textContent = resolved.text ?? render.text ?? "";

    // Wires bound to the CLOSED root/editable — page-injected nodes never reach them.
    if (!this.editableWired) {
      editable.addEventListener("input", () => void this.onEditInput());
      root.addEventListener("click", (ev) => void this.onEditableClick(ev));
      this.editableWired = true;
    }

    this.reflectTrust("extension", true);
    this.setAttribute("receipts", String(resolved.receiptCount ?? 0));
    if (resolved.commitment) this.setAttribute("commitment", resolved.commitment);
    this.removeAttribute("dirty");
    this.paintBadge(root, "extension", true);

    exposeRootForTest(this, root);
  }

  /** THE KEYED RECONCILER. On every input: read the DOM's new text, diff it into
   *  the minimal patch (engine/wasm side), then REPAINT from the engine's canonical
   *  `currentText()` while PRESERVING the caret — compute the caret offset before the
   *  repaint, restore it after. The caret is "keyed" on its character offset, so a
   *  keystroke never blows the cursor back to the start. */
  private async onEditInput(): Promise<void> {
    const root = this.closedShadow();
    const editable = root.querySelector(".doc-edit") as HTMLElement | null;
    if (!editable) return;
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    const newText = editable.textContent ?? "";

    let edit: DocTextEditResponse;
    try {
      edit = (await this.text.request({ op: "applyEdit", uri: this.uri, text: newText })) as DocTextEditResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      return;
    }
    if (!edit.ok) {
      note.textContent = `⚠ ${edit.error || "edit failed"}`;
      return;
    }

    // Compute the caret offset BEFORE the repaint, repaint from the engine's
    // canonical text, then RESTORE the caret to that offset (clamped).
    const offset = caretOffset(root, editable);
    const canonical = edit.text ?? newText;
    editable.textContent = canonical;
    if (offset !== null) setCaret(root, editable, offset);

    // Surface the minimal-patch summary (proves a replaced word = 1 add + 1 tombstone,
    // NOT a full rewrite) and the dirty (unpublished-edits) state.
    const added = edit.atomsAdded ?? 0;
    const tombstoned = edit.atomsTombstoned ?? 0;
    this.setAttribute("atoms-added", String(added));
    this.setAttribute("atoms-tombstoned", String(tombstoned));
    if (edit.dirty) this.setAttribute("dirty", "");
    const patchinfo = root.querySelector(".patchinfo") as HTMLElement;
    patchinfo.textContent =
      `last edit: +${added} atom, −${tombstoned} atom (minimal patch, not a rewrite) · unpublished`;
  }

  /** The publish affordance: commit the accumulated edits as one real verified turn,
   *  routed through the engine's injected consent (the faithful reading) BEFORE any
   *  commit; then re-verify the light-client boundary. */
  private async onEditableClick(ev: Event): Promise<void> {
    const target = ev.target as HTMLElement | null;
    const btn = target?.closest?.('button[data-turn="publish-text"]') as HTMLElement | null;
    if (!btn) return;
    const root = this.closedShadow();
    const note = root.querySelector(".note") as HTMLElement;
    note.textContent = "";
    setDisabled(root, true);

    let pub: DocTextPublishResponse;
    try {
      pub = (await this.text.request({ op: "publishText", uri: this.uri })) as DocTextPublishResponse;
    } catch (e) {
      note.textContent = `⚠ ${String((e as Error)?.message ?? e)}`;
      setDisabled(root, false);
      return;
    }

    if (pub.refused) {
      note.textContent = `⚠ publish refused: ${pub.reason || "refused"}`;
      this.setAttribute("publish-refused", "");
    } else if (pub.ok) {
      this.removeAttribute("publish-refused");
      this.removeAttribute("dirty");
      this.setAttribute("receipts", String(pub.receiptCount ?? 0));
      if (pub.commitment) this.setAttribute("commitment", pub.commitment);
      if (pub.substrateMatches) this.setAttribute("substrate-matches", "");
      else this.removeAttribute("substrate-matches");
      const patchinfo = root.querySelector(".patchinfo") as HTMLElement;
      patchinfo.textContent = "published — the edits are a verified turn a stranger can re-check";
    }

    // Re-verify the badge from the engine (the stranger's light-client check).
    const verify = (await this.text.request({ op: "verifyText", uri: this.uri })) as DocTextVerifyResponse;
    this.reflectTrust(verify.tier, verify.verified);
    if (!verify.verified) {
      this.removeAttribute("verified");
      this.setAttribute("error", "");
    }
    if (verify.commitment) this.setAttribute("commitment", verify.commitment);
    if (typeof verify.receiptCount === "number") this.setAttribute("receipts", String(verify.receiptCount));
    this.paintBadge(root, verify.tier, verify.verified);
    setDisabled(root, false);
  }
}

function setDisabled(root: ShadowRoot, disabled: boolean): void {
  (root.querySelectorAll(".deos-button, button") as NodeListOf<HTMLButtonElement>).forEach((b) => {
    b.disabled = disabled;
  });
}

// ── the keyed reconciler's caret machinery ────────────────────────────────────
// The editable lives in a CLOSED shadow root. Selections inside a closed root are
// scoped to that root — Chromium exposes `ShadowRoot.getSelection()`; elsewhere
// (Firefox) `document.getSelection()` reaches into the shadow tree. We try the
// shadow-scoped selection first, then fall back.

function getSelectionFor(root: ShadowRoot): Selection | null {
  const anyRoot = root as unknown as { getSelection?: () => Selection | null };
  if (typeof anyRoot.getSelection === "function") {
    const s = anyRoot.getSelection();
    if (s) return s;
  }
  return typeof document !== "undefined" ? document.getSelection() : null;
}

/** The caret's character offset within the editable (the sum of text before it),
 *  or `null` if the caret is not inside the editable. */
function caretOffset(root: ShadowRoot, editable: HTMLElement): number | null {
  const sel = getSelectionFor(root);
  if (!sel || sel.rangeCount === 0) return null;
  const range = sel.getRangeAt(0);
  if (!editable.contains(range.startContainer) && range.startContainer !== editable) return null;
  const pre = range.cloneRange();
  pre.selectNodeContents(editable);
  try {
    pre.setEnd(range.startContainer, range.startOffset);
  } catch {
    return null;
  }
  return pre.toString().length;
}

/** Restore the caret to `offset` characters into the editable (clamped). After a
 *  repaint the editable holds a single text node (plain prose). */
function setCaret(root: ShadowRoot, editable: HTMLElement, offset: number): void {
  const sel = getSelectionFor(root);
  if (!sel) return;
  let node = editable.firstChild;
  if (!node || node.nodeType !== Node.TEXT_NODE) {
    node = document.createTextNode(editable.textContent ?? "");
    editable.replaceChildren(node);
  }
  const len = node.textContent?.length ?? 0;
  const off = Math.max(0, Math.min(offset, len));
  const range = document.createRange();
  range.setStart(node, off);
  range.collapse(true);
  sel.removeAllRanges();
  sel.addRange(range);
}

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

/** Test hook (never populated in production): expose the closed root so the
 *  harness can drive/read it. Gated on an explicit global flag, exactly like
 *  `<dregg-poll>`'s `__dreggPollRoots`. */
function exposeRootForTest(el: Element, root: ShadowRoot): void {
  if ((globalThis as unknown as { __DREGG_EXPOSE_SHADOW_FOR_TEST__?: boolean }).__DREGG_EXPOSE_SHADOW_FOR_TEST__) {
    const reg = ((globalThis as unknown as { __dreggDocRoots?: WeakMap<Element, ShadowRoot> }).__dreggDocRoots ??=
      new WeakMap());
    reg.set(el, root);
  }
}

/** Register the `<dregg-doc>` custom element (idempotent). Call from the content script. */
export function registerDocElement(): void {
  if (typeof customElements === "undefined" || customElements === null) return; // null in Chromium isolated worlds
  if (!customElements.get("dregg-doc")) customElements.define("dregg-doc", DreggDoc);
}
