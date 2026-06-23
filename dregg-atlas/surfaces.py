"""THE SURFACE CENSUS — the single source of truth for every cockpit surface the
atlas bakes + explains.

Grounded in the live cockpit's `Tab` enum (starbridge-v2/src/cockpit/mod.rs) — its
30 tabs — PLUS the dock workspace's dev panes (editor / terminal / chat / agent),
which are not `Tab`s but cap-confined Surface cells inside the paned workspace.

The screenshot `tab` name is the cockpit's own label normalized exactly the way
`Cockpit::select_tab_named` normalizes (ascii-alphanumeric, lowercased). That is
the string the MCP `screenshot` tool / `--render-tab` resolves. We carry it as
`render_tab`; `id` is the stable atlas id; `explainer` is the first-principles
blurb the gallery + the static page show; `deep` (a slug) links the long-form
explainer section; `bake` selects the render path (per-tab vs showcase).
"""

# (id, render_tab, label, bake, deep_slug, explainer)
#   render_tab — normalized name `select_tab_named` matches (label, alnum-lower).
#                None ⇒ no live tab (a dev pane / composite); bake via 'showcase'.
#   bake       — 'tab'      : screenshot with tab=render_tab (the per-surface bake)
#                'showcase' : the --render-showcase composite (no single tab)
SURFACES = [
    # ---- the landing + reflective core -----------------------------------
    ("home", "home", "HOME", "tab", "home",
     "The at-rest landing — the warm front door of the live verified image; "
     "names the running system reflectively (executor · cells · receipts · organs) "
     "with live counts read off the real ledger."),
    ("inspector", "inspector", "INSPECTOR", "tab", "inspector",
     "The moldable inspector (Registry · Spotter · Halo): every object's presentation "
     "faces as a sub-tab strip; the inspector is itself inspectable."),
    ("inspect-act", "inspectact", "INSPECT-ACT", "tab", "inspect-act",
     "The Smalltalk inspect→act→inspect loop: a cell's reflected state plus the "
     "messages it understands, each with a cap badge; firing one commits a real turn."),
    ("workspace", "workspace", "WORKSPACE", "tab", "workspace",
     "The doIt / printIt / inspectIt evaluator — compose an intent, evaluate it in a "
     "forked throwaway world (predict, never mutate), then commit-or-discard."),
    ("wonder", "wonder", "WONDER", "tab", "wonder",
     "The AOL-wonder front door — every cell a pokeable glowing object (glow = real "
     "recent activity) with direct-manipulation halos (inspect / grab / explain)."),
    ("lanes", "lanes", "LANES", "tab", "lanes",
     "The moldable-inspector gadgets made reachable: the predicate composer (caveat "
     "language), the turn builder, the attenuation dial, the macaroon token loop."),
    ("objects", "objects", "OBJECTS", "tab", "objects",
     "The object browser around the accounting axes — cell lifecycle, turn proofs, "
     "nullifiers — a direct reflection of the live ledger + receipt log."),

    # ---- the graph / ocap / link surfaces --------------------------------
    ("graph", "graph", "GRAPH", "tab", "graph",
     "The whole-image ocap delegation graph — cells as nodes, capability grants as "
     "directed edges, laid out by multi-hop delegation depth (the blast radius)."),
    ("web-of-cells", "webofcells", "WEB-OF-CELLS", "tab", "web-of-cells",
     "The cockpit as a native browser of the dregg:// docuverse — attested cross-cell "
     "reads with ledger-drawn origin chrome and the per-viewer affordance membrane."),
    ("links-here", "whatlinkshere", "WHAT-LINKS-HERE", "tab", "links-here",
     "Ted Nelson's two-way link navigable: the real Backlinks witness-graph (who "
     "transcludes ME), projected through the viewer's membrane (link fog-of-war)."),
    ("powerbox", "powerbox", "POWERBOX", "tab", "powerbox",
     "CapDesk's trusted designation flow — a confined app requests authority; the "
     "trusted powerbox presents a picker of what the USER holds and mints an "
     "attenuated cap into the app's c-list via a real grant turn."),

    # ---- the proof / time / replay axis ----------------------------------
    ("proofs", "proofs", "PROOFS", "tab", "proofs",
     "The proof-attach + STARK verification board — each committed turn's verification "
     "tier and the attach/verify route."),
    ("debugger", "debugger", "DEBUGGER", "tab", "debugger",
     "Step + explain a turn against the live world — the time-aware debugger."),
    ("replay", "replay", "REPLAY", "tab", "replay",
     "Deterministic replay / time-travel over the canonical witnessed history."),
    ("time", "time", "⏳ TIME", "tab", "time",
     "The temporal cockpit — time-travel + suspend + fractal meta-debug as one panel: "
     "the rewind scrubber re-derives any past point (root-verified), ⏸ suspends the "
     "real loop (M5 gate), the metastack climbs a reflective tower over the world."),

    # ---- identity / vault / trust ----------------------------------------
    ("cipherclerk", "cipherclerk", "CIPHERCLERK", "tab", "cipherclerk",
     "The sovereign cipherclerk vault — HD-derived identities, macaroon signing."),
    ("trust", "trust", "⚷ TRUST", "tab", "trust",
     "The human-layer 'you cannot lose your own OS' face — your devices, your "
     "guardians-as-faces with the K-of-N threshold drawn, the KEL rotation timeline, "
     "and the ask-your-guardians recovery quorum gauge."),

    # ---- authoring / share / docs ----------------------------------------
    ("editor", "editor", "EDITOR", "tab", "editor",
     "The conserving forest editor — build a turn, validate it (Σδ=0), commit."),
    ("composer", "composer", "COMPOSER", "tab", "composer",
     "The predicate / caveat composer — the attenuable proof-carrying caveat language."),
    ("simulate", "simulate", "SIMULATE", "tab", "simulate",
     "The what-if intent composer — predict a turn's consequences in a forked "
     "throwaway world (the real executor over a deep copy), then commit the identical "
     "turn for real; the live world is untouched until commit."),
    ("docs", "docs", "📄 DOCS", "tab", "docs",
     "The dreggverse document language as a surface — a document IS a cell, an edit IS "
     "a cap-gated turn; a CONFLICT is a first-class state (two live alternatives, each "
     "tagged with its provenance receipt, with a one-click resolving patch)."),
    ("share", "share", "⤳ SHARE", "tab", "share",
     "The share-with-attenuation pre-send editor — cull the frustum (which lenses are "
     "shared), pare the authority (an amplifying choice is refused in-band), verify the "
     "per-viewer membrane preview, and share a revocable rehydratable artifact."),

    # ---- the agentic surfaces --------------------------------------------
    ("agent", "agent", "AGENT", "tab", "agent",
     "The agent surface — an autonomous loop over the image, confined to the "
     "ACP↔ToolGateway seam (every tool-call a cap-gated, witnessed turn)."),
    ("swarm", "swarm", "SWARM", "tab", "swarm",
     "The swarm orchestration surface — N agent panes as confined Surface cells, "
     "coordinating via the notify-edge inbox (EmitEvent → NotifyEdge → async drain)."),
    ("shell", "shell", "SHELL", "tab", "shell",
     "The cap-first command shell over the image — the cockpit's own trusted root."),

    # ---- the browsers + devtools -----------------------------------------
    ("webshell", "webshell", "🌐 WEB-SHELL", "tab", "webshell",
     "A general http(s):// browser surface (distinct from web-of-cells): a real "
     "gpui-component URL bar (Enter-to-go), back/forward/reload, and a content tile "
     "rendered through the Servo SWGL pipeline behind the net-cap allowlist; "
     "fail-closed (a cap refusal shows in-band, the tile never silently blanks)."),
    ("devtools", "devtools", "⚙ DEVTOOLS", "tab", "devtools",
     "Firebug for a verified OS — one tab, three inspector sub-tabs: NETWORK (the data "
     "plane: deliveries / inboxes / wakes / notify-edges), LOG/RECEIPTS (the blocklace "
     "+ receipt timeline console), FEDERATION (committee · epoch · checkpoint · "
     "bridges · revocation)."),

    # ---- the IDE dock panes (Surface cells inside the paned workspace) ----
    # These are NOT Tab variants; they are cap-confined Surface cells living in the
    # dock (PaneGroup/Pane). The atlas bakes them via the showcase composite (the
    # workspace dock is what the showcase renders) and via the Buffer/Terminal tabs.
    ("buffer", "buffer", "BUFFER", "tab", "buffer",
     "The IDE's EDITOR pane — a text buffer as a cap-confined Surface cell (A1); the "
     "editor half of the ⌘K real PTY/editor split."),
    ("terminal", "terminal", "TERMINAL", "tab", "terminal",
     "The IDE's TERMINAL pane — a command surface as a cap-confined Surface cell (A1), "
     "home of the ADOS tool-call seam (a real PTY)."),
    ("dock-workspace", None, "DOCK WORKSPACE", "showcase", "dock-workspace",
     "The self-hosting cockpit dock — editor + terminal + chat + agent as resizable "
     "dock panes (PaneGroup / Pane), the desktop epoch's self-hosting cockpit. Baked "
     "via the showcase composite (the full cockpit, not a single tab)."),

    # ---- EXTERNAL BAKES (committed PNGs from their own e2e/headless bakes) ----
    # These surfaces are NOT cockpit `Tab`s and are not produced by the MCP
    # screenshot tool; each is captured by the run that demonstrates it (a bake
    # that hard-asserts its proofs, or a live e2e). The atlas carries the
    # committed PNG (copied in by shoot.py when bake='external', via `src`) plus a
    # first-principles explainer. Each `src` is a repo path under the parent tree.
    ("self-hosting-loop", None, "SELF-HOSTING LOOP", "external", "self-hosting-loop",
     "Develop dregg INSIDE deos: the firmament editor (a save is a cap-gated SetField "
     "ledger turn) beside a live alacritty PTY running real cargo/rustc — one image. "
     "The bake hard-asserts the receipt grew AND the toolchain ran; "
     "src `starbridge-v2/self-hosting-loop-full.png`."),
    ("zed-workspace", None, "ZED WORKSPACE", "external", "zed-workspace",
     "The full Zed IDE over the cell ledger: a real workspace::Workspace whose Fs IS "
     "the dregg cell ledger; Zed's own project/outline/terminal panels dock + resolve, "
     "and a save through the IDE fires a verified TurnReceipt. (No committed PNG — "
     "the proof is the green full-zed test suite; this is the surface explainer.)"),
    ("web-deos", None, "WEB DEOS (in-browser)", "external", "web-deos",
     "The same gpui cockpit bundled to wasm32 + WebGPU, painting a real frame in a "
     "browser tab over the same in-tab verified executor — one renderer, two platforms. "
     "src `starbridge-v2/web/cockpit-gpui-web-painted.png` (headless Chrome, canvas 2560×1640)."),
    ("servo-page", None, "SERVO REAL PAGE", "external", "servo-page",
     "A real Servo web engine page laid out + rasterized (the surfman / event-loop / "
     "SWGL ceilings cleared): a data: page's CSS box measured, glyphs as 212-color "
     "antialiased text. src `servo-render/servo_real_page_render.png`."),
    ("mud", None, "MUD MULTI-INHABITANT", "external", "mud",
     "A multi-inhabitant MUD where the PHYSICS is the proof: 3 inhabitants / 2 rooms "
     "over the real executor; a door is a cap you lack, items conserve across trades, "
     "a give can't amplify authority, value Σδ=0 — all executor-gated via real receipts. "
     "(No committed PNG — the proof is the 9-test mud suite.)"),
    ("membrane", None, "MULTIPLAYER MEMBRANE", "external", "membrane",
     "The fork-and-stitch primitive: one cap-bounded World::fork (a MembraneFrustum) "
     "carried over the wire, rehydrated into TWO real Worlds under two principals "
     "(anti-substitution), each committing a real turn, then stitched (linear Dead-wins "
     "join, over-authorized confer REFUSED). (No committed PNG — the proof is the "
     "21-test shared_fork suite.)"),
    ("federation", None, "FEDERATION (n=2)", "external", "federation",
     "A real two-node dregg-node federation over QUIC gossip + blocklace consensus: a "
     "faucet turn on A gossips to B and both DAGs converge byte-identically to "
     "consensus-attested finality. (No committed PNG — the proof is the runbook + the "
     "named net/node tests.)"),
    ("unified-boot", None, "THE UNIFIED BOOT", "external", "unified-boot",
     "One window, three panes: a LIVE --node-attached pane (a real running dregg-node's "
     "/status + cells + latest receipt over the wire) beside a FirmamentFs editor and a "
     "live PTY terminal — the cockpit panes standing alongside a real node, not a mock. "
     "src `deos-unified-boot.png`. Honest seam: an editor save commits to the cockpit's "
     "LOCAL World (the node is read-only-synced); a real over-the-wire write-back is a "
     "separate lane (route the save through NodeClient::submit_turn)."),
    ("scripting-js", None, "REFLECTIVE JS SCRIPTING", "external", "scripting-js",
     "Cap-gated Pharo: real SpiderMonkey (mozjs) where the JS objects you touch ARE live "
     "handles into the running image — deos.world.cells() crawls the ledger, "
     "deos.cell(id).reflect() reads the four substances, .as(viewer) is a cap-bounded "
     "frustum (unreachable = absent, never forged), and an applet's affordance fire is a "
     "real verified turn (a receipt). Reflection is a READ (no turns); interaction is "
     "production-under-non-forgeability. (No committed PNG — the proof is the deos-js + "
     "deos-reflect test suites.)"),
    ("deos-reflect", None, "deos-reflect SUBSTRATE", "external", "deos-reflect",
     "The gpui-free cap-bounded reflective substrate, reusable off a bare "
     "dregg_cell::Ledger: substance (four substances + Inspectable, fields read PUBLICLY "
     "so Committed redacts) · graph (OcapGraph: nodes/edges/reachability/layers/cycles) · "
     "frustum (the per-viewer cap-bounded crawl) · affordances (cap-gated projection by "
     "is_attenuation) · present (substrate-pure faces: RawFields · Graph · DomainVisual · "
     "Provenance). The shared shape under both dregg-mcp and the JS scripting env. "
     "(No committed PNG — the proof is the 5/5 deos-reflect test suite.)"),
]


def render_tab_for(s):
    """The MCP `screenshot` tab arg for a surface tuple (None ⇒ showcase bake)."""
    return s[1]


def by_id():
    return {s[0]: s for s in SURFACES}
