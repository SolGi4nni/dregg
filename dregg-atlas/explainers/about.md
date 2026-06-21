# THE DREGG ATLAS

A self-built, interactive map of dregg — a formally verified distributed
object-capability OS where the Lean kernel IS the executor the node runs, and
circuits are emitted from Lean. This atlas was authored by an AI agent CRAWLING
the live verified image through the `dregg-mcp` harness: every state, every cell,
every turn, every refusal here was read or fired against the real embedded
executor (`dregg_sdk::embed::DreggEngine`). Nothing is mocked.

## The three pillars

The **Game Tree** is the reachable state-space of the seeded image. Each node is
a world-state, identified by its post-state Merkle root; each edge is a turn
fired through the verified executor. Green edges committed and advanced the
world; red edges were refused — either by the object-capability gate before any
turn ran (the anti-ghost tooth: required authority not held), or by a kernel
guarantee firing inside the executor (conservation, non-amplification, a
permissions gate). The tree is what an agent living inside dregg can and cannot
do, made visible.

The **Ocap Web** is the capability graph: cells as nodes, capability grants as
directed edges, read off the live ledger. Click a cell to see its seven
presentation faces — the same moldable inspector the cockpit renders.

The **Protocol Reference** is the vocabulary beneath it all: the eight verbs, the
AuthRequired lattice, the four substances (balance, state, capabilities, nonce)
and their conservation, and the refusal taxonomy.

## What a turn is

The one-sentence thesis the whole system turns on: *a turn is the exercise of an
attenuable proof-carrying token over owned state, leaving a verifiable receipt.*
Every committed edge in the game tree is one of those.

## Regenerating this atlas

Everything here is regenerable from the live system:

```
cd dregg-atlas
python3 crawl.py    # walk the state-space via dregg-mcp
python3 shoot.py    # screenshot the 28 cockpit surfaces
python3 build.py    # assemble the site
open site/index.html
```
