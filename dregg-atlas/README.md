# THE DREGG ATLAS

A self-built, offline-explorable interactive map of dregg — the formally verified
distributed object-capability OS. It was authored by an AI agent *crawling the
live verified image* through the `dregg-mcp` harness: every state, cell, turn,
and refusal here was read or fired against the real embedded executor. Nothing is
mocked.

## Open it

Open **`site/index.html`** in any browser (it is fully offline — JS is vendored,
data is inlined). Seven views:

- **Game Tree** — the reachable PROTOCOL state-space as a radial starburst
  (genesis at the centre, depth as colour-graded rings). Each node is a
  world-state (keyed by its post-state Merkle root); each edge a turn fired
  through the verified executor. Click a state for its cell snapshot and its
  committed/refused turns; click to highlight its reachable subtree.
- **UI Tree** — the UI INTERACTION state-space: exploring inside and through the
  cockpit surfaces. A radial DAG (HOME → the 28 surfaces → each surface's internal
  navigations: cycling focus chips, picking lenses, toggling, scrubbing). Each
  node is a distinct *rendered* UI state (screenshot); each edge the interaction
  that reaches it. Click a state for its screenshot + the interactions out of it.
  (Driving the real cockpit headlessly this way also shakes out render bugs —
  260 states rendered with zero panics; four live-animated tabs are excluded, see
  the Anomalies page.)
- **Ocap Web** — cells + the capability grants between them; click a cell for its
  seven presentation faces.
- **UI Atlas** — all 28 cockpit surfaces screenshotted, each with a
  first-principles, code-grounded explainer (click a card → its full page).
- **Protocol** — the deep reference: the thesis, the eight verbs, the four
  substances + conservation, the AuthRequired lattice, the refusal taxonomy, the
  receipt structure.
- **Anomalies** — bugs and inconsistencies the crawl surfaced.
- **About** — what this is and how it was built.

## Regenerate it from the live system

```
cd dregg-atlas

# 0. build the dregg-mcp harness (once)
( cd ../starbridge-v2 && cargo build --release --features native-full --bin dregg-mcp \
                       && cargo build --release --features headless-render --bin starbridge-v2 )

python3 crawl.py    # walk the protocol state-space (DFS, snapshot/restore backtracking)
python3 shoot.py    # screenshot the 28 cockpit surfaces
# the UI tree: BFS-walk the cockpit's UI state-space, screenshot each state
( cd ../starbridge-v2 && ZED_OFFSCREEN_PREFER_CPU=1 \
  ATLAS_UI_NODES=260 target/release/starbridge-v2 --explore-ui ../dregg-atlas/ui-explore )
python3 build.py    # assemble the site
open site/index.html
```

Tunables (env): `ATLAS_DEPTH` (game-tree depth, default 4), `ATLAS_NODES` /
`ATLAS_EDGES` (caps), `ATLAS_XFER` (transfer amount the crawl fires).

## How it works

- `mcp_client.py` — a JSON-RPC stdio client for `dregg-mcp` (the verified-executor
  driving harness; see `../docs/deos/DREGG-MCP.md`).
- `crawl.py` — DFS over the reachable state-space. Backtracking uses the MCP's
  fork-based `snapshot`/`restore` (instant), not a 3-second world reboot. The
  move set at each state is every self-affordance on every cell (peek/touch/write/
  grant) PLUS a cross-cell transfer between every ordered pair (value flow +
  conservation). Bounded by depth + node/edge caps; every bound is logged so a
  truncation is never mistaken for completeness.
- `shoot.py` — drives the MCP `screenshot` tool (the real gpui Cockpit bake) over
  all 28 surfaces.
- `build.py` + `tmpl/` — the site-builder: cytoscape.js + dagre for the graphs,
  the explainers parsed from `explainers/*.md`, the static pages cross-linked to
  the SPA.

The honest scope: the game tree is exhaustive *over the crawled move set* (the
self-affordance vocabulary + cross-cell transfers) up to the depth bound — not
over every possible effect/argument combination, which is unbounded. The move set
and bounds are stated in `data/gametree.json`'s `meta`.
