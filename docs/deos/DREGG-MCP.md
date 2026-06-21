# dregg-mcp — driving the live verified image

`dregg-mcp` is an MCP server that drives the **starbridge-v2 live verified ocap
image** so an agent can inspect, act on, map, and screenshot the real dregg
world while iterating on it. Every tool reads or writes the genuine embedded
executor (`dregg_sdk::embed::DreggEngine` via `starbridge_v2::world::World`) —
there is no mock and no second object model. It is the inspect→act→inspect loop,
the moldable inspector's seven presentation faces, the ocap/affordance maps, and
the headless gpui cockpit bake, exposed as ten tools over JSON-RPC stdio.

## Build & run

```
# the model server (gpui-free, fast, robust)
cd starbridge-v2
cargo build --release --no-default-features --features embedded-executor --bin dregg-mcp

# screenshots additionally need the headless-render cockpit binary
cargo build --release --features headless-render --bin starbridge-v2
```

It is registered in the repo's `.mcp.json` as `dregg-image` (launcher:
`starbridge-v2/scripts/dregg-mcp.sh`, which builds-if-missing then execs). A new
Claude Code session picks it up automatically; the tools then appear as
`mcp__dregg-image__*`.

## The ten tools

| tool | what it does |
|------|--------------|
| `boot {image}` | (re)boot the session world — `demo` (fully-seeded sovereign image) or `empty`. Returns the roster. |
| `survey` | every ledger cell: id, kind, title, balance, cap-edges — the top of the inspectable tree. |
| `inspect {cell,as?,rights?}` | a cell's **seven presentation faces** (raw-fields · graph · affordances · provenance · invariant · source · domain-visual) + the halo ring, as JSON. The reflective inspect-element. |
| `affordances {cell,as?,rights?}` | the messages a cell understands, each with its real effect + the **cap badge** (authorized? for the viewer). Anti-ghost: refused messages are shown, not hidden. |
| `act {cell,message,as?,rights?}` | **fire** a message — a real cap-gated turn through the verified executor. Returns the receipt + reinspected post-state, or the in-band refusal (`by_executor` distinguishes the cap-gate from the executor). Mutates the live world. |
| `spotter {query,as?}` | fuzzy-search every object's every face (the ⌘K palette). |
| `graph {kind,format}` | emit an interaction map — `ocap` (the capability web), `affordance` (object→message→effect), or `interactions` (this session's nav+act trail) — as `json` or Graphviz `dot`. |
| `render {cell,out?}` | render a cell's full inspector view to a self-contained dark-theme HTML page (the portable, annotatable Firebug DOM). |
| `screenshot {out?}` | bake the **real gpui Cockpit element tree**, over this session's driven state (it replays the committed act-trail), to an 800×600 PNG via the headless-render subprocess. |
| `view` | session summary: cells, anchors, acts committed, cells visited. |

Cell handles accept an anchor name (`treasury`/`service`/`user`), a full 64-char
hex id, or a short hex prefix (the ids `survey` prints). `as` inspects/acts AS a
chosen principal (default: the cell itself — the self-operator projection); two
different-cap viewers see different cap badges on the same object.

## The loop, by example

```
survey                                  → 4 cells; user=2a6969…ab90, the issuer well at −1000000
affordances user                        → peek✓ touch✓ write✓ grant✗  (each with its real Effect + required tier)
act user touch                          → committed: IncrementNonce, post-state hash advances
act user grant                          → refused, by_executor=false: required ⊄ held (the cap-gate, before any turn)
inspect user                            → 5 faces (raw-fields/affordances/provenance/graph/domain-visual) + halo
graph ocap dot                          → the capability web (service→user, slot 0/1)
screenshot                              → /tmp/dregg-cockpit.png — the real cockpit, reflecting the touch
```

## The Firebug verdict

The question this harness was built to answer: does the moldable inspector
already give a developer the inspect→understand→act loop that the Firebug era
only gestured at? The honest answer, having driven it:

**Yes, and past it — on three axes Firebug never had.**

1. **Reflective, not DOM-specific.** Firebug inspected one substrate (the HTML
   DOM). Here *every protocol object* is `Presentable` and yields the same seven
   faces — a cell, a capability, a receipt, the inspector *itself*
   (`FocusTarget::ViewCell`), even a suspended world (`DebugFrame`). The
   inspect-element generalizes to the whole system.
2. **Act, with the authority shown.** Firebug let you edit the DOM and watch it
   re-render. Here `act` fires a **real cap-gated verified turn**, and the
   refusal is first-class and *located*: `by_executor:false` means the
   object-capability gate refused before any turn (the anti-ghost tooth);
   `by_executor:true` means a kernel guarantee fired (conservation,
   non-amplification, a permissions gate). You don't just see state — you see the
   *authority* and watch it refuse you in-band.
3. **The image is its own pixels.** `screenshot` doesn't grab a foreign window —
   it bakes the live `Cockpit` element tree to an image over the exact session
   state, the same render path the seL4 desktop PD blits. The thing you inspect
   and the thing you see are one image.

What is *missing* relative to a mature devtools suite, named honestly: a network
panel (the receipt/blocklace timeline is the provenance face, but there is no
live SSE inspector here yet), a performance profiler, and a writable gadget
surface (`CommittingGadget` builds turns from a form; `dregg-mcp` exposes only
the message-firing `act`, not the full gadget construction yet). These are the
next rungs, not foundations.

## What it found on its first drive

A candidate inconsistency, surfaced immediately (the kind of lead the harness
exists to produce): `affordances user` reports `grant` with `required: None`,
yet its cap badge is `authorized: false`, and `act user grant` is refused with
"does not satisfy None". A `None` requirement should always clear. Either the
displayed `required` (the cell-permission tier) and the fire-gate's requirement
(the firmament window-cap tier) are two different authority axes being rendered
under one label, or the badge is computed against a tier the displayed value
doesn't name. Tracked for investigation — see HORIZONLOG.

## Interaction map (seed for the manual)

The `graph` tool emits the maps a user/developer manual is built from. The
static affordance map (object→message→effect, colored by authorization) and the
ocap web are derivable at any time; the `interactions` graph records what an
agent actually did. Render any of them with Graphviz:

```
graph ocap dot        | dot -Tsvg > ocap.svg
graph affordance dot  | dot -Tsvg > affordances.svg
graph interactions dot| dot -Tsvg > session.svg
```
