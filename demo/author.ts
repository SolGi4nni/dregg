/**
 * THE AUTHORING SURFACE — write a `.scene`, hit ▶ Play, watch it compile and play
 * as a REAL verifiable story, in the tab. No server, no extension.
 *
 * This is the authoring HALF of the fiction engine: The Commons page loads a
 * committed `.scene` from disk; here you EDIT the source in a textarea and compile
 * it live. The trick is the committed wasm `StoryWorld::new(sceneSource)` — it takes
 * the `.scene` SOURCE STRING and compiles it fail-closed (an unparseable scene is a
 * `JsError` with a message; NOTHING is minted). On a good compile we mount the real
 * shipping `<dregg-story>` element over that world and play it: choices are real
 * cap-gated verified turns, the receipt chain grows, and `verify()` replays the whole
 * chain — the stranger's check.
 *
 * The compile loop, per ▶ Play:
 *  1. TRIAL COMPILE the editor text through the real wasm ctor (the authoritative
 *     fail-closed gate). On throw → surface the message (localized to a line where we
 *     can) and TEAR DOWN the stage: no half-world is mounted, and any previously
 *     mounted world is removed (fail-closed, never silently kept).
 *  2. On success → a FRESH `StoryEngine` over an `AuthoredWorld` (which mints from the
 *     current source), a FRESH `<dregg-story>` element, and play.
 *
 * Everything the element/engine/wasm touch is the shipping code path. The only
 * page-side pieces are the editor chrome and the auto-approve consent (the author IS
 * the custody in their own tab — every choice is still a real verified turn).
 */

import { StoryEngine, defaultResolveStory, type StoryWorldLike } from "../extension/src/port";
import { setStoryPortFactory, registerStoryElement } from "../extension/src/elements/dregg-story";

declare const window: any;

// ── the well-commented starter story (teaches the DSL by example) ────────────────
const STARTER = `// ── Your story starts here. Edit freely, then hit ▶ Play. ──
// Lines starting with // are comments — the compiler ignores them.

// FRONTMATTER: every story needs an id + a title, between --- fences.
---
id: first_light
title: The Lantern-Keeper
---

// A PASSAGE begins with === and a name. This one is the opening.
=== start

The lighthouse has gone dark, and a ship is due before dawn.
You climb the spiral stair with a cold lantern in your hand.

// A CHOICE is  * [text]  and it NAVIGATES with  -> passage
* [Light the lantern at once]
  ~ lit = 1          // ~ is an EFFECT: it sets a story variable
  -> gallery

* [Search the keeper's desk first]
  -> desk

// ── another passage ──
=== desk

In the drawer: a box of matches and a warning note.
"The great lamp is temperamental. Light the small lantern first."

* [Take the matches and climb on]
  ~ matches = 1
  -> gallery

=== gallery

The lamp room. The sea is black glass below.

// A GATED choice: the condition goes on the SAME LINE as the choice, in { }.
// This one is only takeable once you carry a lit lantern (lit >= 1).
* [Light the great lamp] { lit >= 1 }
  -> saved

// An ordinary choice is always takeable.
* [Feel your way back down for the lantern]
  -> start

=== saved

The beam swings out across the water. Far off, the ship
answers with three long notes and turns for the harbor mouth.

You kept the light. THE END.
`;

// Sample stories fetched from disk (the shipping scenes The Commons plays).
const SAMPLES: Record<string, { label: string; src?: string; text?: string }> = {
  starter: { label: "The Lantern-Keeper (starter)", text: STARTER },
  "the-commons": { label: "The Commons (sample)", src: "/stories/the-commons.scene" },
  "the-drowned-library": { label: "The Drowned Library (sample)", src: "/stories/the-drowned-library.scene" },
};

// ── module state ─────────────────────────────────────────────────────────────────
let CURRENT_SCENE = "";
let currentEngine: StoryEngine | null = null;
let currentUri = "";
let LAST_ERROR: string | null = null;
let LAST_ERROR_LINE: number | null = null;
let mountSeq = 0;

/** A thin adapter over the real wasm `StoryWorld` that mints from the CURRENT source.
 *  The engine calls `new AuthoredWorld(spec.scene)` (spec.scene is undefined via the
 *  stand-in resolver) — so it reads the module-scoped compiled source instead. A
 *  fail-closed ctor throws on an unparseable scene (we validate before ever getting
 *  here, so this only mints a scene we already compiled). */
class AuthoredWorld implements StoryWorldLike {
  private real: any;
  constructor() {
    const Ctor = window.wasm_bindgen?.StoryWorld;
    if (!Ctor) throw new Error("the wasm StoryWorld export is not loaded");
    this.real = new Ctor(CURRENT_SCENE);
  }
  currentPassage(): string { return this.real.currentPassage(); }
  passageProse(): string { return this.real.passageProse(); }
  choicesJson(): string { return this.real.choicesJson(); }
  advance(index: number): string { return this.real.advance(index); }
  verify(): boolean { return this.real.verify(); }
  commitmentHex(): string { return this.real.commitmentHex(); }
  receiptCount(): number { return this.real.receiptCount(); }
}

const $ = (id: string) => document.getElementById(id)!;
const msg = (e: unknown) => String((e as Error)?.message ?? e);
const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));

function escapeHtml(s: string): string {
  return s.replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

// ── the editor (plain textarea + a synced line-number gutter) ─────────────────────
function editorEl(): HTMLTextAreaElement { return $("editor") as HTMLTextAreaElement; }

function syncGutter(): void {
  const ta = editorEl();
  const gutter = $("gutter");
  const n = ta.value.split("\n").length;
  const cur = gutter.childElementCount;
  if (cur !== n) {
    const rows: string[] = [];
    for (let i = 1; i <= n; i++) rows.push(`<span>${i}</span>`);
    gutter.innerHTML = rows.join("");
  }
  gutter.scrollTop = ta.scrollTop;
}

/** Count passages + choices from the source (a cheap live authoring readout — the
 *  wasm remains the authority for whether it actually compiles). */
function counts(text: string): { passages: number; choices: number } {
  const passages = (text.match(/^===\s+\S+/gm) || []).length;
  const choices = (text.match(/^\s*\*\s*\[/gm) || []).length;
  return { passages, choices };
}

function updateCounts(): void {
  const c = counts(editorEl().value);
  $("counts").textContent = `${c.passages} passage${c.passages === 1 ? "" : "s"} · ${c.choices} choice${c.choices === 1 ? "" : "s"}`;
}

// ── error localization ────────────────────────────────────────────────────────────
/** The wasm compile message does NOT carry a line (its Display drops the span). For
 *  the common structural errors we can still point at a line: a `` `passage` `` named
 *  in the message (unknown navigation target) is found where the source navigates to
 *  it. Best-effort — when we cannot localize, we show the bare message honestly. */
function locateError(source: string, message: string): { line: number; text: string } | null {
  const lines = source.split("\n");
  // Any backtick-quoted token in the message (e.g. unknown passage `nowhere`).
  const tick = /`([^`]+)`/.exec(message);
  if (tick) {
    const tok = tick[1];
    const re = new RegExp(`->\\s*${tok.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`);
    for (let i = 0; i < lines.length; i++) if (re.test(lines[i])) return { line: i + 1, text: lines[i].trim() };
    // fall through: the token appears somewhere in the source
    for (let i = 0; i < lines.length; i++) if (lines[i].includes(tok)) return { line: i + 1, text: lines[i].trim() };
  }
  return null;
}

function showError(source: string, message: string): void {
  LAST_ERROR = message;
  const loc = locateError(source, message);
  LAST_ERROR_LINE = loc?.line ?? null;
  const panel = $("error");
  panel.classList.add("live");
  const head = loc ? `Line ${loc.line} — compile failed` : "Compile failed";
  const where = loc ? `<div class="err-line"><span class="ln">${loc.line}</span><code>${escapeHtml(loc.text)}</code></div>` : "";
  panel.innerHTML =
    `<div class="err-head">⚠ ${escapeHtml(head)}</div>` +
    `<div class="err-msg">${escapeHtml(message)}</div>` +
    where +
    `<div class="err-foot">fail-closed — no world was mounted. fix the scene and hit ▶ Play.</div>`;
  $("status").textContent = "compile failed — the scene was not mounted";
  $("statusDot").className = "dot bad";
}

function clearError(): void {
  LAST_ERROR = null;
  LAST_ERROR_LINE = null;
  const panel = $("error");
  panel.classList.remove("live");
  panel.innerHTML = "";
}

/** Tear the stage down to the empty placeholder — used on a compile failure so a
 *  previously mounted world is NEVER silently kept behind an error. */
function teardownStage(): void {
  currentEngine = null;
  const stage = $("stage");
  stage.replaceChildren();
  const ph = document.createElement("div");
  ph.className = "placeholder";
  ph.textContent = "no world mounted — write a scene on the left and hit ▶ Play.";
  stage.appendChild(ph);
  paintChain(0, "", false, null);
}

// ── the receipt chain + verify chrome (the authoring readout) ─────────────────────
function paintChain(receipts: number, commitment: string, verified: boolean, passage: string | null): void {
  const links = Array.from({ length: receipts }, (_, i) => `<span class="link" title="verified turn ${i + 1}">●</span>`).join(
    '<span class="rope">—</span>',
  );
  $("chain").innerHTML =
    `<div class="chain-links">${links || '<span class="link empty">○</span>'}</div>` +
    `<div class="chain-meta">${receipts} verified turn${receipts === 1 ? "" : "s"}` +
    (passage ? ` · at <b>${escapeHtml(passage)}</b>` : "") +
    ` · commitment <code>${escapeHtml((commitment || "").slice(0, 12) || "—")}…</code></div>`;
  const badge = $("verifyBadge");
  if (receipts <= 0 && !verified) {
    badge.className = "verify";
    badge.textContent = "";
  } else if (verified) {
    badge.className = "verify ok";
    badge.textContent = "✓ chain verified — a stranger's replay reproduces every turn.";
  } else {
    badge.className = "verify bad";
    badge.textContent = "⚠ the receipt chain did not replay.";
  }
}

/** Re-read the mounted element's reflected attributes + run the engine's verify
 *  (the stranger's replay) and repaint the authoring chrome. */
async function refreshChrome(): Promise<void> {
  const el = document.getElementById("authored");
  if (!el || !currentEngine) return;
  const receipts = Number(el.getAttribute("receipts") || "0");
  const commitment = el.getAttribute("commitment") || "";
  const passage = el.getAttribute("passage") || "";
  let verified = false;
  try {
    const v = (await currentEngine.handle({ op: "verifyStory", uri: currentUri })) as any;
    verified = !!v.verified;
  } catch { /* keep false */ }
  paintChain(receipts, commitment, verified, passage);
}

// ── mounting the real <dregg-story> element over the compiled world ───────────────
function freshUri(): string {
  return `dregg://story/b3_${Date.now().toString(16)}${Math.floor(Math.random() * 0x10000).toString(16)}`;
}

function mountStory(uri: string): HTMLElement {
  const stage = $("stage");
  stage.replaceChildren();
  const el = document.createElement("dregg-story");
  el.id = "authored";
  el.setAttribute("src", uri);
  const a = document.createElement("a");
  a.href = "https://dregg.net";
  a.textContent = "open the story";
  el.appendChild(a);
  stage.appendChild(el);
  // Repaint the chrome whenever the element reflects a new state (boot, advance).
  const obs = new MutationObserver(() => void refreshChrome());
  obs.observe(el, { attributes: true, attributeFilter: ["receipts", "commitment", "passage", "verified", "error"] });
  return el;
}

async function waitUntil(pred: () => boolean, timeoutMs = 8000): Promise<boolean> {
  const start = Date.now();
  while (!pred()) {
    if (Date.now() - start > timeoutMs) return false;
    await sleep(40);
  }
  return true;
}

/** ▶ PLAY — the compile loop. Returns a summary the driven run reads. */
async function play(text: string): Promise<any> {
  // 1) TRIAL COMPILE through the authoritative wasm ctor (fail-closed).
  const Ctor = window.wasm_bindgen?.StoryWorld;
  if (!Ctor) {
    showError(text, "the wasm StoryWorld export is not loaded");
    teardownStage();
    return { ok: false, error: LAST_ERROR };
  }
  try {
    // Construct (and discard) — this throws with the parser/compiler message on a bad
    // scene, WITHOUT mounting anything. The engine mints its own instance below.
    new Ctor(text);
  } catch (e) {
    showError(text, msg(e));
    teardownStage();
    return { ok: false, error: LAST_ERROR, line: LAST_ERROR_LINE };
  }

  // 2) SUCCESS — a fresh engine over the compiled source + a fresh element.
  clearError();
  CURRENT_SCENE = text;
  currentUri = freshUri();
  currentEngine = new StoryEngine({
    StoryWorld: AuthoredWorld as unknown as { new (): StoryWorldLike },
    resolveStory: defaultResolveStory,
    // The author is the custody in their own tab — auto-approve, but every choice is
    // still a REAL cap-gated verified turn on the world.
    consent: async () => true,
  });

  const seq = ++mountSeq;
  const el = mountStory(currentUri);
  const c = counts(text);
  $("status").textContent = `compiled — ${c.passages} passage${c.passages === 1 ? "" : "s"}, ${c.choices} choice${c.choices === 1 ? "" : "s"}. play it →`;
  $("statusDot").className = "dot ok";

  // Wait for the element to boot verified (or fail closed) so callers see the result.
  await waitUntil(() => seq !== mountSeq || el.hasAttribute("verified") || el.hasAttribute("error"), 8000);
  if (seq !== mountSeq) return { ok: true, superseded: true };
  const mounted = el.hasAttribute("verified");
  await refreshChrome();
  if (!mounted) {
    // The element failed to verify a compiled scene (should not happen) — honest fail.
    showError(text, "the world compiled but did not replay-verify");
    teardownStage();
    return { ok: false, error: LAST_ERROR };
  }
  return { ok: true, passages: c.passages, choices: c.choices, receipts: Number(el.getAttribute("receipts") || "0") };
}

// ── the shadow-root test seam (drive the element's own choice buttons) ────────────
function storyRoot(el: Element): ShadowRoot | undefined {
  const roots = window.__dreggStoryRoots as WeakMap<Element, ShadowRoot> | undefined;
  return roots?.get(el);
}

// ── controls ──────────────────────────────────────────────────────────────────────
async function loadSample(key: string): Promise<void> {
  const s = SAMPLES[key];
  if (!s) return;
  let text = s.text ?? "";
  if (s.src) {
    try {
      const r = await fetch(s.src);
      text = r.ok ? await r.text() : `// could not load ${s.src} (${r.status})`;
    } catch (e) {
      text = `// could not load ${s.src}: ${msg(e)}`;
    }
  }
  editorEl().value = text;
  syncGutter();
  updateCounts();
  await play(text);
}

function wireControls(): void {
  const ta = editorEl();
  ta.addEventListener("input", () => { syncGutter(); updateCounts(); });
  ta.addEventListener("scroll", () => { $("gutter").scrollTop = ta.scrollTop; });
  // Tab inserts two spaces (don't lose focus to the next control).
  ta.addEventListener("keydown", (ev) => {
    if (ev.key === "Tab") {
      ev.preventDefault();
      const s = ta.selectionStart, e = ta.selectionEnd;
      ta.value = ta.value.slice(0, s) + "  " + ta.value.slice(e);
      ta.selectionStart = ta.selectionEnd = s + 2;
      syncGutter();
    }
    // Cmd/Ctrl+Enter → Play.
    if ((ev.metaKey || ev.ctrlKey) && ev.key === "Enter") {
      ev.preventDefault();
      void play(ta.value);
    }
  });

  $("playBtn").addEventListener("click", () => void play(ta.value));
  $("restartBtn").addEventListener("click", () => void play(ta.value));
  ($("sample") as HTMLSelectElement).addEventListener("change", (ev) => {
    void loadSample((ev.target as HTMLSelectElement).value);
  });
}

// ── test seams (also power the "restart"/driven run) ──────────────────────────────
function installTestHooks(): void {
  window.__authorPlay = (text?: string) => play(typeof text === "string" ? text : editorEl().value);
  window.__authorSetText = (t: string) => { editorEl().value = t; syncGutter(); updateCounts(); };
  window.__authorVerify = async () => {
    if (!currentEngine) return { verified: false, receiptCount: 0 };
    return currentEngine.handle({ op: "verifyStory", uri: currentUri });
  };
  window.__authorState = () => {
    const el = document.getElementById("authored");
    return {
      hasElement: !!el,
      mounted: !!el && el.hasAttribute("verified"),
      passage: el?.getAttribute("passage") ?? null,
      receipts: Number(el?.getAttribute("receipts") || "0"),
      error: LAST_ERROR,
      errorLine: LAST_ERROR_LINE,
      counts: counts(editorEl().value),
    };
  };
  /** Advance by clicking the mounted element's OWN choice button (the real
   *  element→engine→wasm turn path), then re-verify. */
  window.__authorAdvance = async (index = 0) => {
    const el = document.getElementById("authored");
    if (!el) return { ok: false, error: "no world mounted" };
    const root = storyRoot(el);
    const buttons = root ? [...root.querySelectorAll<HTMLButtonElement>("button[data-choice]")] : [];
    const btn =
      buttons.find((b) => Number(b.getAttribute("data-choice")) === index && !b.disabled) ||
      buttons.find((b) => !b.disabled);
    if (!btn) return { ok: false, error: "no takeable choice at this passage" };
    const before = Number(el.getAttribute("receipts") || "0");
    btn.click();
    await waitUntil(() => Number(el.getAttribute("receipts") || "0") > before || el.hasAttribute("choice-refused"), 8000);
    await refreshChrome();
    const after = Number(el.getAttribute("receipts") || "0");
    let verified = false;
    try { verified = !!((await currentEngine!.handle({ op: "verifyStory", uri: currentUri })) as any).verified; } catch { /* */ }
    return { ok: after > before, before, after, verified, passage: el.getAttribute("passage") };
  };
}

// ── boot ────────────────────────────────────────────────────────────────────────
async function boot(): Promise<void> {
  const ta = editorEl();
  ta.value = STARTER;
  syncGutter();
  updateCounts();
  wireControls();
  installTestHooks();

  $("status").textContent = "loading the verifiable world…";
  try {
    await window.wasm_bindgen("dregg_wasm_bg.wasm");
    if (!window.wasm_bindgen.StoryWorld) throw new Error("the wasm bundle has no StoryWorld export");
  } catch (e) {
    $("status").textContent = `⚠ ${msg(e)}`;
    $("statusDot").className = "dot bad";
    window.__authorError = msg(e);
    window.__authorReady = true;
    return;
  }

  // The element's test seam (drive its own choice buttons from the page — the exact
  // element→engine→wasm turn path). Set BEFORE the port factory / registration.
  window.__DREGG_EXPOSE_SHADOW_FOR_TEST__ = true;
  setStoryPortFactory(() => ({
    async request(req: any) {
      if (!currentEngine) return { ok: false, tier: "none", verified: false, error: "no world" };
      return currentEngine.handle(req, location.origin);
    },
  }));
  registerStoryElement();

  // Auto-play the starter so the page lands already playing (teaches by doing).
  await play(STARTER);
  window.__authorReady = true;
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", () => void boot());
} else {
  void boot();
}
