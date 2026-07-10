/**
 * THE FORGE — write a `.dungeon` world in text, hit ▶ Play, and it becomes a real
 * attested AI dungeon in the tab: a local model (gemma2:2b) narrates, the WORLD resolves
 * every move, and a hash-chain remembers it. Author → play → verify. No Rust, no recompile.
 *
 * The LEFT pane is a line-numbered `.dungeon` editor (a small commented starter + a sample
 * picker + a cheat-sheet). The RIGHT pane is the live play surface — the same UI family as
 * /vault, speaking ONLY the /game service contract over fetch:
 *   POST /game/author {source} · GET /game/state · POST /game/act {command} · GET /game/verify
 *
 * ▶ Play POSTs the editor text to /game/author, which is FAIL-CLOSED in three stages:
 *   · a SYNTAX error   → {stage:"parse", line, message}          — shown line-pinned, NO world
 *   · SEMANTIC errors  → {stage:"validate", issues:[…]}          — EVERY issue listed, NO world
 *   · else             → {ok:true, warnings, state}              — a fresh world, play it now
 * On any failure the previous world is torn down (never silently kept behind an error).
 */

declare const window: any;

interface Exit { name: string; to: string; toName: string; locked: boolean; gateReason: string | null }
interface RoomView { id: string; name: string; description: string }
interface GameState {
  world: string;
  worldName: string;
  room: RoomView;
  inventory: string[];
  exits: Exit[];
  itemsHere: string[];
  objective: string;
  status: "playing" | "won" | "lost";
  receiptCount: number;
  commitmentHex: string;
  narratorKind: string;
}
interface ActResp {
  ok: boolean;
  narration: string;
  action: unknown;
  actionLabel?: string;
  outcome: "landed" | "refused";
  reason?: string;
  worldNote?: string;
  state: GameState;
}
interface Issue { line: number; severity: "error" | "warning"; message: string }
interface AuthorResp {
  ok: boolean;
  stage?: "parse" | "validate";
  line?: number;
  message?: string;
  issues?: Issue[];
  warnings?: Issue[];
  state?: GameState;
}

const $ = (id: string) => document.getElementById(id)!;

async function jget<T>(url: string): Promise<T> {
  const r = await fetch(url, { headers: { accept: "application/json" } });
  return (await r.json()) as T;
}
async function jpost<T>(url: string, body: unknown): Promise<T> {
  const r = await fetch(url, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body) });
  return (await r.json()) as T;
}
function short(hex: string): string { return hex && hex.length > 12 ? `${hex.slice(0, 8)}…${hex.slice(-6)}` : hex || "—"; }
function escapeHtml(s: string): string { return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!)); }
function titleize(s: string): string { return s.replace(/_/g, " "); }
const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));

// ── the well-commented starter world (teaches the DSL by example) ─────────────────
const STARTER = `# ── Your dungeon starts here. Edit freely, then hit ▶ Play. ──
# Lines starting with #  (or //)  are comments — the parser ignores them.

name: The Candle Crypt                  # flavour — the dungeon's title
start: gatehouse                        # the room you wake in
objective: reach shrine holding relic   # WIN by carrying the relic to the shrine

# A ROOM is:   room <id> "<Name>"   then indented prose, items, and exits.
room gatehouse "The Mossy Gatehouse"
  A cold archway of green stone. A candle rests in a wall-niche, still unlit.
  items: candle                         # things you can 'take' here (comma list)
  exit north -> hall                    # exit <direction> -> <room-id>

room hall "The Long Hall"
  A pillared hall swallowed in dark. Stairs drop into a lightless crypt below.
  exit south -> gatehouse
  # A GATED exit: you may only descend once you HOLD the candle.
  exit down -> crypt requires item candle

room crypt "The Candle Crypt"
  A low crypt of niches. On a stone bier rests a faintly glowing relic.
  items: relic
  exit up -> hall
  exit north -> shrine

room shrine "The Quiet Shrine"
  A domed shrine open to a shaft of grey daylight — the way out.
  exit south -> crypt

# The end: hold the candle, descend, take the relic, carry it to the shrine — you WIN.
`;

// Sample worlds. The starter is inline; the rest are the committed .dungeon files served
// from attested-dm/dungeons/ (so the editor teaches against the real, tested samples).
const SAMPLES: Record<string, { label: string; src?: string; text?: string }> = {
  starter: { label: "The Candle Crypt (starter)", text: STARTER },
  lantern_fen: { label: "The Lantern of the Fen (sample)", src: "/dungeons/lantern_fen.dungeon" },
  ember_observatory: { label: "The Ember Observatory (every construct)", src: "/dungeons/ember_observatory.dungeon" },
  broken: { label: "The Broken Hold (fails validation)", src: "/dungeons/broken.dungeon" },
};

// ── module state ──────────────────────────────────────────────────────────────────
let MOUNTED = false;             // is a live authored world currently playable?
let LAST_ERROR: string | null = null;
let LAST_ERROR_LINE: number | null = null;
let LAST_ISSUES: Issue[] = [];
let busy = false;

// The client-side tale (the DM's prose + the world's verdict per turn). The receipt rail is
// the authoritative ledger; this is the human transcript.
interface LogRow { command: string; narration: string; outcome: string; reason?: string; worldNote?: string; label?: string }
const tale: LogRow[] = [];

// ── the editor (plain textarea + a synced line-number gutter) ─────────────────────
function editorEl(): HTMLTextAreaElement { return $("editor") as HTMLTextAreaElement; }

function syncGutter(): void {
  const ta = editorEl();
  const gutter = $("gutter");
  const n = ta.value.split("\n").length;
  if (gutter.childElementCount !== n) {
    const rows: string[] = [];
    for (let i = 1; i <= n; i++) rows.push(`<span>${i}</span>`);
    gutter.innerHTML = rows.join("");
  }
  gutter.scrollTop = ta.scrollTop;
}

/** A cheap live authoring readout (the service remains the authority for whether it parses). */
function counts(text: string): { rooms: number; exits: number } {
  const rooms = (text.match(/^room\s+\S+/gm) || []).length;
  const exits = (text.match(/^\s*exit\s+/gm) || []).length;
  return { rooms, exits };
}
function updateCounts(): void {
  const c = counts(editorEl().value);
  $("counts").textContent = `${c.rooms} room${c.rooms === 1 ? "" : "s"} · ${c.exits} exit${c.exits === 1 ? "" : "s"}`;
}

// ── the fail-closed error panel (parse: one line-pinned; validate: EVERY issue) ────
function sourceLineText(line: number | null | undefined): string {
  if (!line || line < 1) return "";
  const lines = editorEl().value.split("\n");
  return lines[line - 1] ?? "";
}

function showParseError(line: number, message: string): void {
  LAST_ERROR = message;
  LAST_ERROR_LINE = line || null;
  LAST_ISSUES = [];
  const panel = $("error");
  panel.classList.add("live");
  const head = line > 0 ? `Line ${line} — the world did not parse` : "The world did not parse";
  const where = line > 0
    ? `<div class="err-line"><span class="ln">${line}</span><code>${escapeHtml(sourceLineText(line).trim())}</code></div>`
    : "";
  panel.innerHTML =
    `<div class="err-head">⚠ ${escapeHtml(head)}</div>` +
    `<div class="err-sub">a syntax error — the parser refused the dungeon</div>` +
    `<div class="err-msg">${escapeHtml(message)}</div>` +
    where +
    `<div class="err-foot">fail-closed — no world was mounted. fix the source and hit ▶ Play.</div>`;
  setStatus("bad", "parse failed — no world mounted");
}

function showValidateErrors(issues: Issue[]): void {
  LAST_ISSUES = issues;
  const errs = issues.filter((i) => i.severity === "error");
  LAST_ERROR = errs.map((i) => i.message).join(" · ");
  LAST_ERROR_LINE = errs.find((i) => i.line > 0)?.line ?? null;
  const panel = $("error");
  panel.classList.add("live");
  const rows = issues.map((i) => {
    const cls = i.severity === "error" ? "issue err" : "issue warn";
    const tag = i.severity === "error" ? "error" : "warning";
    const pin = i.line > 0
      ? `<div class="err-line"><span class="ln">${i.line}</span><code>${escapeHtml(sourceLineText(i.line).trim())}</code></div>`
      : "";
    return `<div class="${cls}"><span class="issue-tag">${tag}</span><span class="issue-msg">${escapeHtml(i.message)}</span>${pin}</div>`;
  }).join("");
  panel.innerHTML =
    `<div class="err-head">⚠ ${errs.length} validation ${errs.length === 1 ? "error" : "errors"} — the world is unsound</div>` +
    `<div class="err-sub">it parses, but the walls do not hold together — every issue is listed below</div>` +
    rows +
    `<div class="err-foot">fail-closed — no world was mounted. fix the source and hit ▶ Play.</div>`;
  setStatus("bad", "validation failed — no world mounted");
}

function clearError(): void {
  LAST_ERROR = null;
  LAST_ERROR_LINE = null;
  LAST_ISSUES = [];
  const panel = $("error");
  panel.classList.remove("live");
  panel.innerHTML = "";
}

function renderWarnings(warnings: Issue[] | undefined): void {
  const el = $("warnings");
  if (!warnings || !warnings.length) { el.className = "warnings"; el.innerHTML = ""; return; }
  el.className = "warnings live";
  el.innerHTML =
    `<div class="warn-head">▲ ${warnings.length} advisory ${warnings.length === 1 ? "warning" : "warnings"} — the world still plays</div>` +
    warnings.map((w) => `<div class="warn-row">${w.line > 0 ? `<span class="ln">${w.line}</span>` : ""}<span>${escapeHtml(w.message)}</span></div>`).join("");
}

function setStatus(dot: "ok" | "bad" | "", text: string): void {
  $("status").textContent = text;
  $("statusDot").className = "dot" + (dot ? " " + dot : "");
}

// ── tearing the play surface down (fail-closed: never keep a stale world) ──────────
function teardownStage(): void {
  MOUNTED = false;
  tale.length = 0;
  // The room / narration / banner live INSIDE the stage — replacing it removes them. Only the
  // rail, the verify badge and the warnings panel live outside the stage and are cleared here.
  const stage = $("stage");
  stage.className = "stage empty";
  stage.innerHTML = '<div class="placeholder">no world mounted — write a dungeon on the left and hit ▶ Play.</div>';
  renderChain(0, "");
  const badge = $("verifyBadge"); badge.className = "verify"; badge.textContent = "";
  renderWarnings([]);
}

// ── the play surface (mirrors /vault: room, exits, inventory, items, log, rail) ────
const STAGE_HTML = `
  <div id="narratorKind" class="narrator">…</div>
  <div class="objective"><span class="star">★</span><span id="objectiveText">…</span></div>
  <section class="scene-frame" aria-label="the room">
    <p id="roomName">…</p>
    <p id="roomDesc"></p>
    <div id="narration"><span class="who">the dungeon master</span><span id="narrationText"></span></div>
  </section>
  <div class="cols">
    <div class="panel">
      <h3>ways out</h3>
      <div id="exits" class="exits"></div>
    </div>
    <div class="panel">
      <h3>what you carry</h3>
      <ul id="inventory"></ul>
      <div class="items-sub"><h3>in this room</h3><ul id="itemsHere"></ul></div>
    </div>
  </div>
  <div class="controls">
    <div class="action-row">
      <input id="cmdInput" type="text" placeholder="what do you do?  (e.g. take candle · go down · look)" autocomplete="off" aria-label="what do you do?" />
      <button id="cmdSend" class="ctrl" type="button">act</button>
    </div>
    <div class="quick">
      <button id="lookBtn" class="ctrl" type="button">👁 look</button>
    </div>
  </div>
  <div id="banner" class="banner" role="status" aria-live="polite"><div class="inner"><p id="bannerTitle" class="b-title"></p><p id="bannerBody" class="b-body"></p></div></div>
  <section class="log-frame"><h3>the tale so far</h3><div id="log"></div></section>
`;

function mountStage(): void {
  const stage = $("stage");
  stage.className = "stage live";
  stage.innerHTML = STAGE_HTML;
  const input = $("cmdInput") as HTMLInputElement;
  const send = () => { const v = input.value.trim(); if (!v) return; input.value = ""; act(v).catch((e) => console.error(e)); };
  $("cmdSend").addEventListener("click", send);
  input.addEventListener("keydown", (e) => { if ((e as KeyboardEvent).key === "Enter") send(); });
  $("lookBtn").addEventListener("click", () => act("look").catch((e) => console.error(e)));
  MOUNTED = true;
}

function renderNarratorKind(kind: string) {
  const el = document.getElementById("narratorKind"); if (!el) return;
  if (kind && kind.startsWith("model:")) {
    el.className = "narrator model";
    el.innerHTML = `🧠 narrated by a real local model <code>${escapeHtml(kind.slice("model:".length))}</code> — it may narrate anything; the <b>world</b> resolves every move.`;
  } else {
    el.className = "narrator";
    el.innerHTML = "🎭 <b>deterministic scripted narrator</b> (ollama unreachable) — the world resolution and the receipt rail are <b>real</b>. Bring up <code>gemma2:2b</code> for live narration.";
  }
}

function renderExits(exits: Exit[]) {
  const el = document.getElementById("exits"); if (!el) return;
  if (!exits.length) { el.innerHTML = '<span class="none">no way out from here.</span>'; return; }
  el.innerHTML = exits.map((e) => {
    if (e.locked) {
      return `<button class="exit locked" data-cmd="go ${escapeHtml(e.name)}" type="button">` +
        `<span><span class="dir">${escapeHtml(e.name)}</span> <span class="dest">🔒 ${escapeHtml(e.toName)}</span>` +
        `<span class="reason">barred — ${escapeHtml(e.gateReason || "locked")}</span></span></button>`;
    }
    return `<button class="exit" data-cmd="go ${escapeHtml(e.name)}" type="button">` +
      `<span class="dir">${escapeHtml(e.name)}</span> <span class="dest">→ ${escapeHtml(e.toName)}</span></button>`;
  }).join("");
  el.querySelectorAll<HTMLButtonElement>("button.exit").forEach((b) => b.addEventListener("click", () => act(b.dataset.cmd || "")));
}

function renderInventory(inventory: string[]) {
  const el = document.getElementById("inventory"); if (!el) return;
  el.innerHTML = inventory.length
    ? inventory.map((i) => `<li><span class="item">${escapeHtml(titleize(i))}</span><span class="state">HELD</span></li>`).join("")
    : '<li class="empty">— empty-handed —</li>';
}

function renderItemsHere(items: string[]) {
  const el = document.getElementById("itemsHere"); if (!el) return;
  if (!items.length) { el.innerHTML = '<li class="empty">— nothing to take —</li>'; return; }
  el.innerHTML = items.map((i) =>
    `<li class="here-row"><span class="item">${escapeHtml(titleize(i))}</span>` +
    `<button class="take" data-cmd="take ${escapeHtml(i)}" type="button">take</button></li>`
  ).join("");
  el.querySelectorAll<HTMLButtonElement>("button.take").forEach((b) => b.addEventListener("click", () => act(b.dataset.cmd || "")));
}

function renderRoom(s: GameState) {
  const rn = document.getElementById("roomName"); if (rn) rn.textContent = s.room.name;
  const rd = document.getElementById("roomDesc"); if (rd) rd.textContent = s.room.description;
  const ot = document.getElementById("objectiveText"); if (ot) ot.textContent = s.objective;
  renderExits(s.exits);
  renderInventory(s.inventory);
  renderItemsHere(s.itemsHere);
}

function renderChain(count: number, commitmentHex: string) {
  const links = $("chainLinks");
  const parts: string[] = [];
  for (let i = 0; i < Math.max(count, 0); i++) { if (i) parts.push('<span class="rope">—</span>'); parts.push("✓"); }
  links.innerHTML = parts.join("") || '<span class="empty">— no turns yet —</span>';
  $("chainMeta").innerHTML = `<b>${count}</b> move${count === 1 ? "" : "s"} landed as verified turns · running commitment <code>${short(commitmentHex)}</code>`;
}

async function renderVerifyBadge(): Promise<boolean> {
  const badge = $("verifyBadge");
  try {
    const { verified, receiptCount } = await jget<{ verified: boolean; receiptCount: number }>("/game/verify");
    badge.className = verified ? "verify ok" : "verify bad";
    badge.textContent = verified
      ? `✓ the whole ledger re-verifies as a hash chain — ${receiptCount} turn${receiptCount === 1 ? "" : "s"}, each authentic, injection-free, prev-linked, binding its typed move`
      : "✗ the ledger failed to re-verify";
    return verified;
  } catch (e) {
    badge.className = "verify bad";
    badge.textContent = "✗ verify unreachable: " + String((e as any)?.message ?? e);
    return false;
  }
}

function renderLog() {
  const el = document.getElementById("log"); if (!el) return;
  if (!tale.length) { el.innerHTML = '<p class="empty">The world waits in the dark. What do you do?</p>'; return; }
  el.innerHTML = tale.map((e) => {
    const refused = e.outcome === "refused";
    return `<div class="entry ${refused ? "refused" : "landed"}">` +
      `<div class="cmd">you: <b>${escapeHtml(e.command)}</b>${e.label ? ` &middot; <span>${escapeHtml(e.label)}</span>` : ""}</div>` +
      (e.narration ? `<div class="prose">${escapeHtml(e.narration)}</div>` : "") +
      (refused
        ? `<div class="verdict">⛔ refused — ${escapeHtml(e.reason || "the world disposed")}<span style="font-weight:400;color:var(--ink-faint)"> (no receipt — the room did not move)</span></div>`
        : `<div class="verdict">✓ landed — a verified turn</div>` + (e.worldNote ? `<div class="worldnote">${escapeHtml(e.worldNote)}</div>` : "")) +
      `</div>`;
  }).join("");
  el.scrollTop = el.scrollHeight;
}

function renderBanner(status: string, worldName?: string) {
  const b = $("banner");
  if (status === "won") {
    b.className = "banner show won";
    $("bannerTitle").textContent = "★ You escape into the light.";
    $("bannerBody").textContent = `You carried the prize to the goal of ${worldName || "your dungeon"}. Every step is a verified turn on the receipt rail — replay it and the chain holds.`;
  } else if (status === "lost") {
    b.className = "banner show lost";
    $("bannerTitle").textContent = "☠ The dungeon keeps you.";
    $("bannerBody").textContent = "You fell in the dark. Hit ▶ Play to forge it fresh — the same gates bite from the start.";
  } else {
    b.className = "banner";
    $("bannerTitle").textContent = "";
    $("bannerBody").textContent = "";
  }
}

// ── the one action path (only meaningful while a world is MOUNTED) ─────────────────
function setBusy(on: boolean) {
  for (const id of ["cmdSend", "cmdInput", "lookBtn", "playBtn", "restartBtn"]) {
    const el = document.getElementById(id) as any; if (el) el.disabled = on;
  }
}

async function act(command: string): Promise<ActResp> {
  command = String(command || "").trim();
  if (!command) throw new Error("empty command");
  if (!MOUNTED) throw new Error("no world mounted");
  if (busy) throw new Error("busy");
  busy = true; setBusy(true);
  try {
    const resp = await jpost<ActResp>("/game/act", { command });
    const nt = document.getElementById("narrationText"); if (nt) nt.textContent = resp.narration || "(the dungeon master says nothing)";
    tale.push({ command, narration: resp.narration, outcome: resp.outcome, reason: resp.reason, worldNote: resp.worldNote, label: resp.actionLabel });
    renderRoom(resp.state);
    renderLog();
    renderChain(resp.state.receiptCount, resp.state.commitmentHex);
    renderBanner(resp.state.status, resp.state.worldName);
    const verified = await renderVerifyBadge();
    window.__FORGE_STATE = {
      status: resp.state.status, receiptCount: resp.state.receiptCount, commitmentHex: resp.state.commitmentHex,
      roomId: resp.state.room.id, inventory: resp.state.inventory, narratorKind: resp.state.narratorKind,
      verified, lastOutcome: resp.outcome, lastReason: resp.reason || null, lastOk: resp.ok,
    };
    return resp;
  } finally { busy = false; setBusy(false); }
}

// ── ▶ PLAY — POST the editor text to /game/author and mount (or fail closed) ───────
async function play(text: string): Promise<AuthorResp> {
  if (busy) throw new Error("busy");
  busy = true; setBusy(true);
  try {
    setStatus("", "forging the world…");
    let resp: AuthorResp;
    try {
      resp = await jpost<AuthorResp>("/game/author", { source: text });
    } catch (e) {
      showParseError(0, "could not reach the /game service: " + String((e as any)?.message ?? e));
      teardownStage();
      return { ok: false };
    }

    if (!resp.ok) {
      // FAIL-CLOSED: tear the previous world down first, THEN surface the errors.
      teardownStage();
      if (resp.stage === "parse") showParseError(resp.line ?? 0, resp.message ?? "the source did not parse");
      else if (resp.stage === "validate") showValidateErrors(resp.issues ?? []);
      else showParseError(0, resp.message ?? "the world could not be authored");
      return resp;
    }

    // SUCCESS — a fresh authored world. Mount the play surface and render its opening state.
    clearError();
    mountStage();
    const s = resp.state!;
    renderNarratorKind(s.narratorKind || "scripted");
    const nt = document.getElementById("narrationText");
    if (nt) nt.textContent = `You stand at the threshold of ${s.worldName || "your dungeon"}. What do you do?`;
    renderRoom(s);
    renderChain(s.receiptCount, s.commitmentHex);
    renderBanner(s.status, s.worldName);
    renderLog();
    await renderVerifyBadge();
    renderWarnings(resp.warnings);
    const c = counts(text);
    setStatus("ok", `forged — ${c.rooms} room${c.rooms === 1 ? "" : "s"}, ${c.exits} exit${c.exits === 1 ? "" : "s"}. play it →`);
    window.__FORGE_STATE = {
      worldName: s.worldName, status: s.status, receiptCount: s.receiptCount, commitmentHex: s.commitmentHex,
      roomId: s.room.id, inventory: s.inventory, narratorKind: s.narratorKind,
    };
    return resp;
  } finally { busy = false; setBusy(false); }
}

// ── controls ───────────────────────────────────────────────────────────────────────
async function loadSample(key: string): Promise<void> {
  const s = SAMPLES[key];
  if (!s) return;
  let text = s.text ?? "";
  if (s.src) {
    try {
      const r = await fetch(s.src);
      text = r.ok ? await r.text() : `# could not load ${s.src} (${r.status})`;
    } catch (e) {
      text = `# could not load ${s.src}: ${String((e as any)?.message ?? e)}`;
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
  ta.addEventListener("keydown", (ev) => {
    if (ev.key === "Tab") {
      ev.preventDefault();
      const s = ta.selectionStart, e = ta.selectionEnd;
      ta.value = ta.value.slice(0, s) + "  " + ta.value.slice(e);
      ta.selectionStart = ta.selectionEnd = s + 2;
      syncGutter();
    }
    if ((ev.metaKey || ev.ctrlKey) && ev.key === "Enter") { ev.preventDefault(); void play(ta.value); }
  });
  $("playBtn").addEventListener("click", () => void play(ta.value));
  $("restartBtn").addEventListener("click", () => void play(ta.value));
  ($("sample") as HTMLSelectElement).addEventListener("change", (ev) => void loadSample((ev.target as HTMLSelectElement).value));
}

// ── test seams (also power the driven run) ─────────────────────────────────────────
function installTestHooks(): void {
  window.__forgePlay = (text?: string) => play(typeof text === "string" ? text : editorEl().value);
  window.__forgeSetText = (t: string) => { editorEl().value = t; syncGutter(); updateCounts(); };
  window.__forgeSample = (key: string) => loadSample(key);
  window.__forgeAct = (c: string) => act(c);
  window.__forgeVerify = () => jget("/game/verify");
  window.__forgeState = () => ({
    mounted: MOUNTED,
    error: LAST_ERROR,
    errorLine: LAST_ERROR_LINE,
    issues: LAST_ISSUES,
    counts: counts(editorEl().value),
    roomId: (window.__FORGE_STATE && window.__FORGE_STATE.roomId) || null,
    receipts: (window.__FORGE_STATE && window.__FORGE_STATE.receiptCount) || 0,
    status: (window.__FORGE_STATE && window.__FORGE_STATE.status) || null,
    worldName: (window.__FORGE_STATE && window.__FORGE_STATE.worldName) || null,
  });
}

// ── boot ────────────────────────────────────────────────────────────────────────
async function boot(): Promise<void> {
  const ta = editorEl();
  ta.value = STARTER;
  syncGutter();
  updateCounts();
  wireControls();
  installTestHooks();
  teardownStage();

  try {
    // Author + play the starter so the page lands already playing (teaches by doing).
    await play(STARTER);
    window.__FORGE_READY = true;
  } catch (e) {
    window.__FORGE_ERROR = String((e as any)?.stack ?? e);
    showParseError(0, "could not reach the /game service: " + String((e as any)?.message ?? e));
    window.__FORGE_READY = true;
  }
  await sleep(0);
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", () => void boot());
} else {
  void boot();
}
