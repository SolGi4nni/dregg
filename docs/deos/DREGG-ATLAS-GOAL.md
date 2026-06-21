# /goal — THE DREGG ATLAS (overnight, exhaustive)

Paste the block below into `/goal`. It is self-contained and assumes the
`dregg-mcp` harness (this session built it: `starbridge-v2/src/bin/dregg_mcp.rs`,
registered in `.mcp.json` as `dregg-image`; manual at `docs/deos/DREGG-MCP.md`).

---

Build **THE DREGG ATLAS**: an exhaustive, self-built, interactive map of the
entire dregg system — its game tree, its UI, and its protocol — that I author by
CRAWLING the live verified image with the `dregg-mcp` harness and understanding
it myself. Work all night across as many context windows as it takes. Bank a
commit after every cluster of progress (per the project laws: green-or-bust,
teach-what-is, never `git add -A`, unsigned commits OK, main loop commits by file
set, leave ember's unrelated uncommitted work alone). Log every bug/inconsistency
the crawl finds to `HORIZONLOG.md` in the same breath. Update a running
`docs/deos/DREGG-ATLAS-PROGRESS.md` so any relaunch reorients instantly.

THREE CO-EQUAL PILLARS, all at MAXIMUM depth (do not cheap out, do not scope
down — "exhaustive" is the bar):

1. **THE GAME TREE** (the centerpiece). From the seeded world, crawl the
   reachable state-space as a tree/DAG: at each state enumerate every authorized
   affordance across every cell, fire each through the real executor, record
   `(state-digest, cell, message, effect, outcome, reason, receipt, next-state-
   digest)`, then `rewind` and try the next. Dedup states by digest; bound by a
   configurable depth (start ~6 plies) and breadth, and LOG every bound so a
   truncation is never mistaken for completeness. Capture the full refusal
   taxonomy (cap-gate `by_executor:false` vs executor-guarantee `by_executor:true`
   — conservation / non-amplification / permissions). This is "visualize the game
   tree": every node a world-state, every edge a turn, colored committed vs
   refused.

2. **THE UI ATLAS**. Screenshot ALL 28 cockpit surfaces (the `screenshot` tool's
   `tab` param; sizes ≥1280x832 so nothing truncates) AND the 7 presentation
   faces (raw-fields/graph/affordances/provenance/invariant/source/domain-visual)
   for every object kind. For each surface write a first-principles explainer:
   what it IS, what it shows, how to use it, how it maps to the protocol beneath.

3. **THE PROTOCOL REFERENCE**. The 8 verbs/effects, the `AuthRequired` lattice
   (with the `None`-as-top subtlety — see the cap-badge anomaly in HORIZONLOG),
   the capability web, the refusal taxonomy, the four substances + conservation
   (BALANCE_SUM=0). Ground every claim in the code (cite file:line) and the live
   crawl, never memory.

DELIVERABLE — a regenerable SITE-BUILDER + its output:
- `dregg-atlas/` — a builder (Rust or a small static generator; your call) that
  ingests the crawl JSON (`dregg-mcp export`), the screenshots, the game-tree
  data, and the explainers, and emits a self-contained site under
  `dregg-atlas/site/` (vendored JS — no CDN; it must open offline via
  `index.html`).
- The site is BOTH, cross-linked: (a) a single interactive SPA — cytoscape.js (or
  d3) graphs you pan/zoom/expand: the ocap web AND the game tree as live graphs;
  click a node → its faces + screenshot + affordances + my explainer; click an
  edge → the action + outcome + reason; AND (b) a browsable static reference (a
  page per surface / object kind / effect / refusal-class / state-class),
  hyperlinked to and from the SPA.
- An "anomalies" page surfacing every bug the crawl found, each with its repro.

METHOD: drive everything through `dregg-mcp` (boot/survey/inspect/affordances/
act/rewind/spotter/graph/render/screenshot/export/protocol). FIRST verify the
foundation: build `dregg-mcp` at `native-full` and confirm its world matches the
cockpit (8 cells, not the lean build's 4 — the HORIZONLOG census finding); if the
seeds still diverge, find out why and make it honest. Re-render the screenshot
binary (`cargo build --release --features headless-render --bin starbridge-v2`)
if the bake changed. Use `Explore`/`general-purpose` subagents for parallel
crawling and code-grounding of explainers; you (the main loop) integrate, build
the site, verify it renders, and commit. Keep the atlas regenerable end-to-end
from one command. Don't stop until all three pillars are deep and the site opens
and is genuinely explorable — then write a final summary to the progress doc.
