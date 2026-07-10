/**
 * THE SUNKEN VAULT — a playable dungeon where the AI narrates and the WORLD resolves.
 *
 * A local model (gemma2:2b) narrates each room and each action, but its prose has NO
 * authority: every move is resolved deterministically by the engine (`resolve_action`).
 * You cannot narrate through a locked door, take an absent item, or win without carrying
 * the amulet to the gate. A legal move lands as one verified chain turn; a refused move
 * leaves the world unchanged and lands no receipt.
 *
 * This page speaks ONLY the /game service contract over fetch (no extension, no wasm):
 *   GET /game/state · POST /game/act {command} · GET /game/verify · POST /game/reset
 * It NEVER fabricates an outcome — the narration, the refusal, and the receipt rail all
 * come from the service. The page renders the ledger, not the story.
 */

declare const window: any;

interface Exit { name: string; to: string; toName: string; locked: boolean; gateReason: string | null }
interface RoomView { id: string; name: string; description: string }
interface GameDef { id: string; name: string; blurb: string; objective: string }
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
function escapeHtml(s: string): string { return String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]!)); }
function titleize(s: string): string { return s.replace(/_/g, " "); }

// The client-side tale (the DM's prose per turn + the world's verdict). The authoritative
// ledger is the receipt rail; this is the human-readable transcript.
interface LogRow { command: string; narration: string; outcome: string; reason?: string; worldNote?: string; label?: string }
const tale: LogRow[] = [];

// ── narratorKind, displayed HONESTLY ─────────────────────────────────────────
function renderNarratorKind(kind: string) {
  const el = $("narratorKind");
  if (kind && kind.startsWith("model:")) {
    el.className = "narrator model";
    el.innerHTML = `🧠 narrated by a real local model <code>${escapeHtml(kind.slice("model:".length))}</code> — it may narrate anything; the <b>world</b> resolves every move.`;
  } else {
    el.className = "narrator";
    el.innerHTML = "🎭 <b>narration is a deterministic scripted narrator</b> (ollama unreachable) — the world resolution, the capability gate, and the receipt rail are <b>real</b>. Bring up <code>gemma2:2b</code> for live narration.";
  }
}

// ── the game picker ──────────────────────────────────────────────────────────
// The registry is served by /game/list; the current world by /game/state. Clicking a card
// resets the session over that world and re-renders. The room/inventory/exits UI is generic
// (it renders whatever /game/state returns), so every game plays through the same surface.
let GAMES: GameDef[] = [];
let currentWorld = "";

function renderPicker() {
  const el = $("gameCards");
  if (!GAMES.length) { el.innerHTML = '<span class="empty">— no games registered —</span>'; return; }
  el.innerHTML = GAMES.map((g) => {
    const current = g.id === currentWorld;
    return `<button class="game-card ${current ? "current" : ""}" data-world="${escapeHtml(g.id)}" type="button">` +
      `<span class="g-name">${escapeHtml(g.name)}${current ? '<span class="g-badge">now playing</span>' : ""}</span>` +
      `<span class="g-blurb">${escapeHtml(g.blurb)}</span>` +
      `<span class="g-obj">★ ${escapeHtml(g.objective)}</span></button>`;
  }).join("");
  el.querySelectorAll<HTMLButtonElement>("button.game-card").forEach((b) => {
    b.addEventListener("click", () => {
      const w = b.dataset.world || "";
      if (w && w !== currentWorld) reset(w).catch((e) => console.error(e));
    });
  });
}

function renderNowPlaying(worldName: string) {
  $("nowPlaying").textContent = worldName || "…";
}

// ── the room, exits, inventory, items ────────────────────────────────────────
function renderExits(exits: Exit[]) {
  const el = $("exits");
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
  el.querySelectorAll<HTMLButtonElement>("button.exit").forEach((b) => {
    b.addEventListener("click", () => act(b.dataset.cmd || ""));
  });
}

function renderInventory(inventory: string[]) {
  const el = $("inventory");
  el.innerHTML = inventory.length
    ? inventory.map((i) => `<li><span class="item">${escapeHtml(titleize(i))}</span><span class="state">HELD</span></li>`).join("")
    : '<li class="empty">— empty-handed —</li>';
}

function renderItemsHere(items: string[]) {
  const el = $("itemsHere");
  if (!items.length) { el.innerHTML = '<li class="empty">— nothing to take —</li>'; return; }
  el.innerHTML = items.map((i) =>
    `<li class="here-row"><span class="item">${escapeHtml(titleize(i))}</span>` +
    `<button class="take" data-cmd="take ${escapeHtml(i)}" type="button">take</button></li>`
  ).join("");
  el.querySelectorAll<HTMLButtonElement>("button.take").forEach((b) => {
    b.addEventListener("click", () => act(b.dataset.cmd || ""));
  });
}

function renderRoom(s: GameState) {
  $("roomName").textContent = s.room.name;
  $("roomDesc").textContent = s.room.description;
  $("objectiveText").textContent = s.objective;
  renderExits(s.exits);
  renderInventory(s.inventory);
  renderItemsHere(s.itemsHere);
}

// ── the receipt rail ─────────────────────────────────────────────────────────
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

// ── the narration log ────────────────────────────────────────────────────────
function renderLog() {
  const el = $("log");
  if (!tale.length) { el.innerHTML = '<p class="empty">The vault waits in the dark. What do you do?</p>'; return; }
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

// ── the win / lose banner ────────────────────────────────────────────────────
function renderBanner(status: string) {
  const b = $("banner");
  if (status === "won") {
    b.className = "banner show won";
    $("bannerTitle").textContent = "★ You escape into the light.";
    $("bannerBody").textContent = "The Drowned Amulet is carried through the broken portcullis. Every step is a verified turn on the receipt rail — replay it and the chain holds.";
  } else if (status === "lost") {
    b.className = "banner show lost";
    $("bannerTitle").textContent = "☠ The vault keeps another bone.";
    $("bannerBody").textContent = "You fell in the dark. Restart the vault to try again — the same gates bite from the shore.";
  } else {
    b.className = "banner";
    $("bannerTitle").textContent = "";
    $("bannerBody").textContent = "";
  }
}

// ── the one action path ──────────────────────────────────────────────────────
let busy = false;
function setBusy(on: boolean) {
  for (const id of ["cmdSend", "cmdInput", "lookBtn", "cheatBtn", "resetBtn"]) {
    const el = document.getElementById(id) as any; if (el) el.disabled = on;
  }
}

async function act(command: string): Promise<ActResp> {
  command = String(command || "").trim();
  if (!command) throw new Error("empty command");
  if (busy) throw new Error("busy");
  busy = true; setBusy(true);
  try {
    const before = window.__VAULT_STATE ? window.__VAULT_STATE.receiptCount : 0;
    const beforeCommit = window.__VAULT_STATE ? window.__VAULT_STATE.commitmentHex : "";
    const beforeRoom = window.__VAULT_STATE ? window.__VAULT_STATE.roomId : "";
    const resp = await jpost<ActResp>("/game/act", { command });

    // The AI's prose leads the scene; the world's verdict follows.
    $("narrationText").textContent = resp.narration || "(the dungeon master says nothing)";
    tale.push({ command, narration: resp.narration, outcome: resp.outcome, reason: resp.reason, worldNote: resp.worldNote, label: resp.actionLabel });

    renderRoom(resp.state);
    renderLog();
    renderChain(resp.state.receiptCount, resp.state.commitmentHex);
    renderBanner(resp.state.status);
    const verified = await renderVerifyBadge();

    window.__VAULT_STATE = {
      status: resp.state.status,
      receiptCount: resp.state.receiptCount,
      commitmentHex: resp.state.commitmentHex,
      beforeCount: before,
      beforeCommit,
      beforeRoom,
      roomId: resp.state.room.id,
      inventory: resp.state.inventory,
      narratorKind: resp.state.narratorKind,
      verified,
      lastOutcome: resp.outcome,
      lastReason: resp.reason || null,
      lastOk: resp.ok,
    };
    return resp;
  } finally { busy = false; setBusy(false); }
}

function applyWorld(s: GameState) {
  currentWorld = s.world || currentWorld;
  renderNowPlaying(s.worldName || "");
  renderPicker();
}

async function loadState(): Promise<GameState> {
  const s = await jget<GameState>("/game/state");
  applyWorld(s);
  renderNarratorKind(s.narratorKind || "scripted");
  renderRoom(s);
  renderChain(s.receiptCount, s.commitmentHex);
  renderBanner(s.status);
  await renderVerifyBadge();
  window.__VAULT_STATE = {
    world: s.world, worldName: s.worldName,
    status: s.status, receiptCount: s.receiptCount, commitmentHex: s.commitmentHex,
    beforeCount: s.receiptCount, beforeCommit: s.commitmentHex, beforeRoom: s.room.id,
    roomId: s.room.id, inventory: s.inventory, narratorKind: s.narratorKind,
  };
  return s;
}

// Reset the session. Pass a world id to SWITCH games; omit it to restart the CURRENT world
// (the service defaults to the sunken vault only when nothing has been selected yet — so the
// committed run-vault driver, which resets with no argument on a fresh boot, still gets the vault).
async function reset(world?: string): Promise<GameState> {
  const body = world ? { world } : (currentWorld ? { world: currentWorld } : {});
  const { state } = await jpost<{ ok: boolean; state: GameState }>("/game/reset", body);
  tale.length = 0;
  applyWorld(state);
  $("narrationText").textContent = `You stand at the threshold of ${state.worldName || "the dungeon"}. What do you do?`;
  renderNarratorKind(state.narratorKind || "scripted");
  renderRoom(state);
  renderLog();
  renderChain(state.receiptCount, state.commitmentHex);
  renderBanner(state.status);
  await renderVerifyBadge();
  window.__VAULT_STATE = {
    world: state.world, worldName: state.worldName,
    status: state.status, receiptCount: state.receiptCount, commitmentHex: state.commitmentHex,
    beforeCount: state.receiptCount, beforeCommit: state.commitmentHex, beforeRoom: state.room.id,
    roomId: state.room.id, inventory: state.inventory, narratorKind: state.narratorKind,
  };
  return state;
}

// ── boot ─────────────────────────────────────────────────────────────────────
async function boot() {
  try {
    try { GAMES = await jget<GameDef[]>("/game/list"); } catch (e) { console.error("could not load /game/list", e); GAMES = []; }
    await loadState();
    renderLog();

    const input = $("cmdInput") as HTMLInputElement;
    const send = () => { const v = input.value.trim(); if (!v) return; input.value = ""; act(v).catch((e) => console.error(e)); };
    $("cmdSend").addEventListener("click", send);
    input.addEventListener("keydown", (e) => { if ((e as KeyboardEvent).key === "Enter") send(); });
    $("lookBtn").addEventListener("click", () => act("look").catch((e) => console.error(e)));
    $("cheatBtn").addEventListener("click", () => act("go down").catch((e) => console.error(e)));
    $("resetBtn").addEventListener("click", () => reset().catch((e) => console.error(e)));

    window.__VAULT_READY = true;
  } catch (e) {
    window.__VAULT_ERROR = String((e as any)?.stack ?? e);
    const badge = $("verifyBadge");
    badge.className = "verify bad";
    badge.textContent = "✗ could not reach the /game service: " + String((e as any)?.message ?? e);
  }
}

// Driver hooks (the same path the buttons take).
window.__vaultAct = (c: string) => act(c);
window.__vaultReset = (world?: string) => reset(world);
window.__vaultLoad = () => loadState();
window.__vaultGames = () => GAMES;

boot();
