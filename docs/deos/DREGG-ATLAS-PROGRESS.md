# THE DREGG ATLAS — progress (overnight build)

*Running log so any relaunch reorients instantly. Goal spec: `DREGG-ATLAS-GOAL.md`.*

## State (2026-06-21) — FIRST FULL ATLAS RENDERS

**Milestone: the atlas opens and is explorable** (verified via Chrome headless).
Game Tree (225 states / 1008 transitions, 567 committed / 441 refused; depth 4),
Ocap Web (4 cells + cap edges), UI Atlas (28 surface screenshots + explainers),
Protocol reference, Anomalies, About — all cross-linked, offline (`site/index.html`).
The KEY unblock: MCP `snapshot`/`restore` (fork-based, 0.000s) replaced the 3s
`rewind` reboot — depth-4 crawl now runs in ~2min (was timing out).

## (earlier) State (2026-06-21, in progress)

**Foundation — DONE.** The `dregg-mcp` harness drives the real verified executor
(`starbridge-v2/src/bin/dregg_mcp.rs`, committed `586d15a22`). Crawl primitives
landed: `rewind` (game-tree backtracking), `export` (full dump), `protocol`,
plus `screenshot` at any size/tab. The 4-vs-8 census is resolved (cockpit adds
reflexive UI cells via `with_node`; the 4-cell `demo_world` is the protocol
substrate). HORIZONLOG carries the findings.

**The atlas pipeline — built, running.** Under `dregg-atlas/`:
- `mcp_client.py` — JSON-RPC stdio client for dregg-mcp (verified working).
- `crawl.py` — walks the reachable state-space (BFS, dedup by post-state digest,
  bounded by depth + node/edge caps, every bound logged). Emits
  `data/{protocol,cells,gametree}.json`. Optimized to only reboot after a
  committed move (refused moves don't mutate). Depth-1 verified (10 states / 16
  transitions); depth-3 crawl running.
- `shoot.py` — screenshots all 28 cockpit surfaces at 1280×832 via the gpui bake;
  emits `data/surfaces.json`. Running.
- `build.py` — the site-builder: ingests the data + screenshots + explainers,
  emits the SPA (`site/index.html` + `app.js`, vendored cytoscape.js + dagre,
  offline) AND cross-linked static pages (`site/pages/`).
- `tmpl/{index.html,app.js,atlas.css}` — the SPA: Game Tree + Ocap Web as live
  cytoscape graphs with detail panels, a screenshot gallery, the protocol
  reference, and the anomalies list.

## Next (deepen toward exhaustive)

1. Land the first full build (gametree + screenshots + site renders) and
   screenshot-verify it opens.
2. Deepen the game tree (depth 4–5; add an `undo`-based DFS to the MCP so it
   stops rebooting per move — the current perf ceiling).
3. Per-cell + per-surface + per-effect static pages, all cross-linked.
4. Author the full explainer set (every surface, every face, every effect, every
   refusal class) grounded in code (file:line).
5. Expand the crawl to richer start states (create cells, transfers, grants,
   attenuate/revoke) so the game tree shows the whole verb vocabulary.
6. Anomalies page from every inconsistency the crawl surfaces.

## Anomalies found so far (also in HORIZONLOG)
- `AuthRequired::None` cap-badge inversion (a None-required affordance reports
  unauthorized for all non-None holders).
- Cell census 4-vs-8 (resolved: reflexive UI cells).
