# THE DREGG ATLAS

A self-built, offline-explorable interactive map of dregg — the formally verified
distributed object-capability OS. It was authored by an AI agent *crawling the
live verified image* through the `dregg-mcp` harness: every state, cell, turn,
and refusal here was read or fired against the real embedded executor. Nothing is
mocked.

## Open it

Open **`site/index.html`** in any browser (it is fully offline — JS is vendored,
data is inlined). The views, newcomer-first:

- **Surfaces** *(the default landing)* — every cockpit surface screenshotted (the
  `Tab` enum's 30 surfaces plus the dock dev panes), each with a first-principles,
  code-grounded explainer and the components it is built from (click a card → its
  full page). The surfaces render inside the **coherent five-mode frame**
  (`cockpit/frame.rs`, `docs/deos/COCKPIT-UX.md`): a persistent top bar (identity
  cell + cap-badge · live ledger clock · ⌘K palette · ⌘J dock), a left rail of the
  five modes — **Inhabit · Author · Dev · Inspect · Operate** — a mode sub-nav, and
  a collapsible dev dock. The gallery groups the surfaces by their mode. This is
  the wonder-first impression: look at the live OS before reading a word about it.
- **Cells & Caps** — the object-capability graph read straight off the live ledger:
  cells as nodes, capability grants as directed edges. Click a cell for its
  balance, its affordances (the messages it understands), and its presentation
  faces — the same moldable inspector the cockpit renders.
- **Turns** — *what a turn is*, shown small. The near-genesis frontier: genesis,
  every distinct move out of it, one more hop. Each node is a world-state (keyed by
  its post-state Merkle root); each edge a turn fired through the verified executor
  — green committed and advanced the world, red was refused (with the reason: the
  cap-gate before any turn, or a kernel guarantee). The whole move vocabulary is
  visible without a 600-state combinatorial dump (the full reachable space is
  regenerable but just explodes the same handful of moves — see *honest scope*).
- **Protocol** — the reference: the thesis, the eight verbs, the four substances +
  conservation, the AuthRequired lattice, the refusal taxonomy, the receipt
  structure, the presentation faces.
- **Components** — the gpui-component widget pillar: the visual building blocks the
  cockpit is built from. Each widget names what it is, its variants, and the
  surfaces that render it; the catalog marks which are *used live in the cockpit
  today* (a grep of the cockpit tree) vs *available* in the palette.
- **Web** — the adept view: the cross-linked hypermedia map over every object
  (cell · surface · component · effect · verb) with typed edges and a type filter.
  Every object carries a stable id, so anything cross-links to anything; ⌘K jumps
  to any object by name.
- **About** — what this is and how it was built.

## Regenerate it from the live system

```
cd dregg-atlas

# 0. build the dregg-mcp harness + the headless-render binary (once). The
#    workspace is UNIFIED (one root `target/`); mcp_client.py finds the binaries
#    in `<repo>/target/release/` (falling back to the old per-crate path).
( cd ../starbridge-v2 && cargo build --release --features native-full \
                       --bin dregg-mcp --bin starbridge-v2 )

python3 crawl.py    # walk the protocol state-space + emit the hypermap (MCP `map`
                    # tool merged in) + the components pillar (a source grep)
python3 shoot.py    # screenshot every cockpit surface (the surfaces.py census;
                    # --no-mcp emits the manifest only, for a later screenshot pass)
python3 verify.py   # ORACLE: assert conservation + well-formedness across the crawled state-space
python3 build.py    # assemble the site
open site/index.html
```

Tunables (env): `ATLAS_DEPTH` (crawl depth, default 4), `ATLAS_NODES` /
`ATLAS_EDGES` (caps), `ATLAS_XFER` (transfer amount the crawl fires). The crawl
still walks the full bounded state-space (for the oracle's conservation check);
the **Turns** view renders only its near-genesis frontier — the full space is
the same few moves exploded across states, so the shape of a turn is legible
without the bloat.

## How it works

- `mcp_client.py` — a JSON-RPC stdio client for `dregg-mcp` (the verified-executor
  driving harness; see `../docs/deos/DREGG-MCP.md`).
- `crawl.py` — DFS over the reachable state-space. Backtracking uses the MCP's
  fork-based `snapshot`/`restore` (instant), not a 3-second world reboot. The
  move set at each state is every self-affordance on every cell (peek/touch/write/
  grant) PLUS a cross-cell transfer between every ordered pair (value flow +
  conservation). Bounded by depth + node/edge caps; every bound is logged so a
  truncation is never mistaken for completeness.
- `surfaces.py` — the canonical SURFACE CENSUS (the single source of truth): the
  cockpit's 30 `Tab`s + the dock dev panes, each with its MCP screenshot tab name,
  bake path (`tab` vs `showcase`), explainer-section slug, and blurb. Imported by
  both `shoot.py` and `build.py`.
- `shoot.py` — drives the MCP `screenshot` tool (the real gpui Cockpit bake) over
  every surface in the census. Reuses a prior PNG when a re-bake isn't possible, so
  a new MCP only needs to fill the new surfaces.
- `components.py` — the COMPONENTS pillar emitter: a curated catalog of the
  gpui-component widget set (name · what-it-is · variants · module) joined with a
  LIVE grep of `starbridge-v2/src/cockpit/` so the "used in deos / on which surface"
  edges are never stale. Emits `data/components.json` with stable ids + typed edges.
- `crawl.py`'s hypermap — synthesizes a cross-linked typed graph (cell → face →
  affordance → effect → ocap-edge) AND merges the MCP `map` tool's authoritative
  backbone when present → `data/hypermap.json`.
- `build.py` + `tmpl/` — the site-builder: cytoscape.js + dagre for the graphs,
  the explainers parsed from `explainers/*.md`, the static pages cross-linked to
  the SPA (including a static `pages/components.html`).

The honest scope: the game tree is exhaustive *over the crawled move set* (the
self-affordance vocabulary + cross-cell transfers) up to the depth bound — not
over every possible effect/argument combination, which is unbounded. The move set
and bounds are stated in `data/gametree.json`'s `meta`.
