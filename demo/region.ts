/**
 * THE OVERWORLD MAP — an inline-SVG picture of the REGION: the bundled dungeons as LOCATIONS
 * joined by travel EDGES, some GATED on clearing a prerequisite. Echoes the room-map visualizer's
 * style (roommap.ts): a BFS-leveled column grid, directed arrows, a LOCKED road drawn distinctly
 * (dashed + red, its gate reason on hover), the CURRENT location highlighted, CLEARED locations
 * marked with a check, and reachable-now locations lit. No libraries, no CDN — deterministic inline
 * SVG. Each node links to that dungeon (/vault, whose picker opens the registered games).
 *
 * The data is exactly what `GET /game/region` returns. Completion is honest: a location is `completed`
 * only when the service credited a genuinely Won + verified session for its game (single-player,
 * server-memory progress in this first slice). Travel is verified-completion-gated: a road opens when
 * its prerequisite is cleared.
 */

interface RegionLoc {
  id: string; name: string; blurb: string; gameId: string;
  registered: boolean; completed: boolean; current: boolean; isCurrentSession: boolean; available: boolean;
}
interface RegionEdge { from: string; to: string; gate: string | null; open: boolean; locked: boolean; gateReason: string | null }
interface RegionView {
  region: { id: string; name: string; blurb: string };
  start: string; current: string; clearedCount: number; total: number;
  locations: RegionLoc[]; edges: RegionEdge[];
  progress: { location: string; completed: string[] };
  note: string;
}

const NODE_W = 168;
const NODE_H = 62;
const COL_GAP = 74;
const ROW_GAP = 26;
const PAD = 30;
const COL_STEP = NODE_W + COL_GAP;
const ROW_STEP = NODE_H + ROW_GAP;

function esc(s: string): string {
  return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}
function truncate(s: string, n: number): string {
  return s.length > n ? s.slice(0, n - 1).trimEnd() + "…" : s;
}
function clip(cx: number, cy: number, tx: number, ty: number): [number, number] {
  const dx = tx - cx, dy = ty - cy;
  const hw = NODE_W / 2 + 4, hh = NODE_H / 2 + 4;
  if (dx === 0 && dy === 0) return [cx, cy];
  const sx = dx === 0 ? Infinity : hw / Math.abs(dx);
  const sy = dy === 0 ? Infinity : hh / Math.abs(dy);
  const s = Math.min(sx, sy);
  return [cx + dx * s, cy + dy * s];
}

/** Render the region graph into `container` (legend + one inline SVG). Stable layout; safe to re-call. */
export function renderRegionMap(container: HTMLElement, view: RegionView): void {
  if (!container) return;
  const rooms = view.locations;
  if (!rooms.length) { container.innerHTML = '<div class="rm-empty">no region to map yet.</div>'; return; }

  const byId = new Map<string, RegionLoc>();
  for (const r of rooms) byId.set(r.id, r);

  // Undirected adjacency for LEVEL assignment (a road connects both ways for layout).
  const adj = new Map<string, Set<string>>();
  const link = (a: string, b: string) => {
    if (!byId.has(a) || !byId.has(b)) return;
    if (!adj.has(a)) adj.set(a, new Set());
    if (!adj.has(b)) adj.set(b, new Set());
    adj.get(a)!.add(b); adj.get(b)!.add(a);
  };
  for (const e of view.edges) link(e.from, e.to);

  // Root the layout at the region START (stable, position-independent) so the picture does not
  // reshuffle as progress changes — only the highlighting moves.
  const ordered = rooms.map((r) => r.id).sort();
  const root = byId.has(view.start) ? view.start : ordered[0];
  const level = new Map<string, number>();
  const queue: string[] = [root];
  level.set(root, 0);
  let maxLevel = 0;
  while (queue.length) {
    const id = queue.shift()!;
    const l = level.get(id)!;
    maxLevel = Math.max(maxLevel, l);
    for (const nb of Array.from(adj.get(id) || []).sort()) {
      if (!level.has(nb)) { level.set(nb, l + 1); queue.push(nb); }
    }
  }
  for (const id of ordered) if (!level.has(id)) level.set(id, maxLevel + 1);
  const lastLevel = Math.max(...Array.from(level.values()));

  const cols: string[][] = [];
  for (let l = 0; l <= lastLevel; l++) cols.push([]);
  for (const id of ordered) cols[level.get(id)!].push(id);

  const pos = new Map<string, { x: number; y: number }>();
  let maxRows = 0;
  for (let l = 0; l < cols.length; l++) {
    maxRows = Math.max(maxRows, cols[l].length);
    cols[l].forEach((id, row) => {
      pos.set(id, { x: PAD + l * COL_STEP + NODE_W / 2, y: PAD + row * ROW_STEP + NODE_H / 2 });
    });
  }
  const width = PAD * 2 + (cols.length - 1) * COL_STEP + NODE_W;
  const height = PAD * 2 + Math.max(1, maxRows - 1) * ROW_STEP + NODE_H;

  // ── edges ──
  const edgeSvg: string[] = [];
  for (const e of view.edges) {
    const a = pos.get(e.from), b = pos.get(e.to);
    if (!a || !b) continue;
    const dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy) || 1;
    const off = 5, px = (-dy / len) * off, py = (dx / len) * off;
    const [sx, sy] = clip(a.x + px, a.y + py, b.x + px, b.y + py);
    const [ex, ey] = clip(b.x + px, b.y + py, a.x + px, a.y + py);
    const cls = e.locked ? "rm-edge locked" : "rm-edge";
    const marker = e.locked ? "url(#rg-arrow-locked)" : "url(#rg-arrow)";
    const toName = byId.get(e.to)?.name || e.to;
    const title = e.locked ? `road to ${toName} — barred: ${e.gateReason || "locked"}` : `road to ${toName}`;
    edgeSvg.push(
      `<line class="${cls}" x1="${sx.toFixed(1)}" y1="${sy.toFixed(1)}" x2="${ex.toFixed(1)}" y2="${ey.toFixed(1)}" marker-end="${marker}"><title>${esc(title)}</title></line>`
    );
  }

  // ── nodes (each an anchor to the dungeon) ──
  const nodeSvg: string[] = [];
  for (const r of rooms) {
    const p = pos.get(r.id)!;
    const x = p.x - NODE_W / 2, y = p.y - NODE_H / 2;
    const cls = ["rg-node"];
    if (r.current) cls.push("current");
    if (r.completed) cls.push("cleared");
    else if (r.available) cls.push("available");
    else cls.push("sealed");
    const label = truncate(r.name, 18);
    const mark = r.completed ? "✓ cleared" : r.current ? "you are here" : r.available ? "open" : "sealed";
    // Registered games open in the /vault picker; venom-deep is wired but not yet pickable.
    const href = r.registered ? `/vault?world=${encodeURIComponent(r.gameId)}` : `/vault`;
    const you = r.current
      ? `<circle class="rg-you-dot" cx="${p.x.toFixed(1)}" cy="${(y - 9).toFixed(1)}" r="4"></circle>`
      : "";
    nodeSvg.push(
      `<a class="rg-link" href="${esc(href)}" data-loc="${esc(r.id)}" data-state="${r.completed ? "cleared" : r.current ? "current" : r.available ? "available" : "sealed"}">` +
      `<g class="${cls.join(" ")}">` +
        you +
        `<rect x="${x.toFixed(1)}" y="${y.toFixed(1)}" width="${NODE_W}" height="${NODE_H}" rx="12"></rect>` +
        `<text class="rg-label" x="${p.x.toFixed(1)}" y="${(p.y - 4).toFixed(1)}" text-anchor="middle">${esc(label)}</text>` +
        `<text class="rg-mark" x="${p.x.toFixed(1)}" y="${(p.y + 15).toFixed(1)}" text-anchor="middle">${esc(mark)}</text>` +
        `<title>${esc(r.name)} — ${esc(r.blurb)}</title>` +
      `</g></a>`
    );
  }

  const W = Math.ceil(width), H = Math.ceil(height);
  const svg =
    `<svg class="regionmap-svg" viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" ` +
    `aria-label="region map: ${esc(String(rooms.length))} dungeons, ${esc(String(view.clearedCount))} cleared" preserveAspectRatio="xMinYMin meet">` +
    `<defs>` +
      `<marker id="rg-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">` +
        `<path class="rg-ahead" d="M0,0 L10,5 L0,10 z"></path></marker>` +
      `<marker id="rg-arrow-locked" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">` +
        `<path class="rg-ahead locked" d="M0,0 L10,5 L0,10 z"></path></marker>` +
    `</defs>` +
    `<g class="rg-edges">${edgeSvg.join("")}</g>` +
    `<g class="rg-nodes">${nodeSvg.join("")}</g>` +
    `</svg>`;

  const legend =
    `<div class="rm-legend">` +
      `<span class="rm-key rg-key-cleared"><span class="rm-swatch"></span>cleared</span>` +
      `<span class="rm-key rg-key-current"><span class="rm-swatch"></span>you are here</span>` +
      `<span class="rm-key rg-key-available"><span class="rm-swatch"></span>open road</span>` +
      `<span class="rm-key rg-key-sealed"><span class="rm-swatch"></span>sealed</span>` +
      `<span class="rm-key rm-key-locked"><span class="rm-swatch"></span>barred road</span>` +
    `</div>`;

  container.innerHTML = legend + `<div class="rm-scroll">${svg}</div>`;
}

// ── the page wiring ────────────────────────────────────────────────────────────
declare global {
  interface Window {
    __REGION_READY?: boolean;
    __REGION_ERROR?: string | null;
    __REGION_VIEW?: RegionView | null;
    __regionRefresh?: () => Promise<RegionView>;
  }
}

async function fetchRegion(): Promise<RegionView> {
  const r = await fetch("/game/region", { headers: { accept: "application/json" } });
  if (!r.ok) throw new Error(`GET /game/region → ${r.status}: ${await r.text()}`);
  return (await r.json()) as RegionView;
}

function paintProgress(view: RegionView): void {
  const bar = document.getElementById("progress");
  if (bar) {
    const pct = view.total ? Math.round((view.clearedCount / view.total) * 100) : 0;
    bar.innerHTML =
      `<div class="prog-head"><b>${view.clearedCount} / ${view.total}</b> dungeons cleared</div>` +
      `<div class="prog-track"><div class="prog-fill" style="width:${pct}%"></div></div>` +
      `<div class="prog-note">${esc(view.note)}</div>`;
  }
  const title = document.getElementById("region-name");
  if (title) title.textContent = view.region.name;
  const blurb = document.getElementById("region-blurb");
  if (blurb) blurb.textContent = view.region.blurb;
}

async function refresh(): Promise<RegionView> {
  const view = await fetchRegion();
  window.__REGION_VIEW = view;
  const map = document.getElementById("map");
  if (map) renderRegionMap(map, view);
  paintProgress(view);
  return view;
}

window.__regionRefresh = refresh;

async function boot(): Promise<void> {
  try {
    await refresh();
    window.__REGION_READY = true;
  } catch (e) {
    window.__REGION_ERROR = String((e as any)?.stack ?? e);
    const map = document.getElementById("map");
    if (map) map.innerHTML =
      `<div class="rm-empty">The region needs the game service. Start it and set <code>DM_PORT</code>, then reload.<br><small>${esc(String((e as any)?.message ?? e))}</small></div>`;
  }
}

const refreshBtn = document.getElementById("refresh");
if (refreshBtn) refreshBtn.addEventListener("click", () => { refresh().catch(() => {}); });

boot();
