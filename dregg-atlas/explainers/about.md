# THE DREGG ATLAS

A self-built, interactive map of dregg — a formally verified distributed
object-capability OS where the Lean kernel IS the executor the node runs, and
circuits are emitted from Lean. This atlas was authored by an AI agent CRAWLING
the live verified image through the `dregg-mcp` harness: every state, every cell,
every turn, every refusal here was read or fired against the real embedded
executor (`dregg_sdk::embed::DreggEngine`). Nothing is mocked.

## How to read it

The atlas is laid out newcomer-first.

**Surfaces** — the default landing — is every rendered surface of the live
cockpit, shot from the real embedded executor, grouped by the five modes
(Inhabit · Author · Dev · Inspect · Operate). Start here: look at the live OS
before reading a word about it. Click a shot to enlarge, click through for its
explainer and the components it is built from.

**Cells & Caps** is the object-capability graph: cells as nodes, capability
grants as directed edges, read straight off the ledger. Click a cell to see its
balance, the messages it understands, and its presentation faces — the same
moldable inspector the cockpit renders.

**Turns** is *what a turn is*, shown small. Each node is a world-state
(identified by its post-state Merkle root); each edge is a turn fired through the
verified executor. Green committed and advanced the world; red was refused —
either by the object-capability gate before any turn ran (the anti-ghost tooth:
required authority not held), or by a kernel guarantee firing inside the
executor (conservation, non-amplification, a permissions gate). This view shows
the near-genesis frontier: the whole move vocabulary, not a combinatorial dump.
The reachable state-space is far larger, but it is the same handful of moves
exploded across states — so the shape of a turn is fully legible here.

**Protocol** is the vocabulary beneath it all: the thesis, the eight verbs, the
AuthRequired lattice, the four substances (balance, state, capabilities, nonce)
and their conservation, the refusal taxonomy, and the presentation faces.

**Components** is the gpui-component widget set the cockpit is built from, and
**Web** is the adept view — every object and the typed edges between them, with a
⌘K spotter to jump anywhere by name.

## What a turn is

The one-sentence thesis the whole system turns on: *a turn is the exercise of an
attenuable proof-carrying token over owned state, leaving a verifiable receipt.*
Every committed edge in the Turns view is one of those.

## Regenerating this atlas

Everything here is regenerable from the live system:

```
cd dregg-atlas
python3 crawl.py    # walk the state-space via dregg-mcp
python3 shoot.py    # screenshot every cockpit surface
python3 build.py    # assemble the site
open site/index.html
```

## Compatibility view (for timetravelers)

The live atlas needs a modern browser. A pure-HTML-4.01 graceful-degradation floor — no script, no canvas, just images and `<map>` image-maps, working in any user-agent back to the dawn of the web — lives at [ie6/index.html](ie6/index.html). The live cockpit degrades the same way: where a browser cannot run the wasm model, it can be driven as a server-rendered frame via image-maps.
