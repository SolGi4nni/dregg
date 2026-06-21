## home
The HOME tab is the live image's front door — the first surface you meet when the verified object-capability image boots. It is not a window-manager scene but a *portal*: a greeting that says you have arrived inside a running, verified image where every object is yours to inspect and drive. The panel renders `LandingPortal::build(&world)` (`cockpit.rs:4829`), a pure gpui-free text model that projects the live `World` — cells, receipts, the image commitment, the organs, the dynamics — into titled section cards (`landing.rs:1`).

What it shows: a masthead headline and subtitle, plus a row of liveness pills computed live each frame — `● live`, `embedded verified executor`, the block height `h{w.height()}`, the cell count, and the receipt count (`cockpit.rs:4851-4855`). Below the masthead, each `PortalSection` becomes a card whose lines are real strings colored by a semantic `Tone`, closing on an invitation-to-act line.

How you use it: you read it. The home tab is self-describing — the image tells you what it is made of, in its own words, with live numbers that prove it is actually running (the cell/receipt/height counts are read from the real ledger, not mocked). Under the hood the portal reflects the REAL system: the heart is `dregg_turn::executor::TurnExecutor` wrapped by `World`, the organs are surveyed via `OrganSurvey`, the receipts are the executor's own `TurnReceipt` chain.

## inspector
The INSPECTOR tab (`moldable_panel`, `cockpit.rs:3275`) is the moldable inspector: a Pharo-GT-style surface where every protocol object offers a *set* of named presentations rather than one fixed view. It is built on the presentation spine in `presentable.rs`, which generalizes `reflect.rs`'s single `Inspectable` field-tree into seven `PresentationKind`s (RawFields, Graph, DomainVisual, Affordances, Provenance, Invariant, Source), with `RawFields` as the mandatory universal floor (`presentable.rs:56-72`).

What it shows: pick a focused cell (the focus chip cycles through the image's cells); the `Registry` builds its `Halo` — a per-object direct-manipulation ring (the universal Inspect/Grab/Explain plus per-kind extensions like a capability's Attenuate, `presentable.rs:553-613`). A lens-family picker selects which presentation set to view, and the chosen object's set renders as a sub-tab strip, each tab one `Presentation`, drawn through the single generic body widget (`cockpit.rs:3494-3531`).

How you use it: click the focus chip to aim the camera at a different object, click a lens or sub-tab to switch presentation, or drive the Spotter (`🔍`) — a ⌘K-style search over *every live object's every presentation*, ranked by `palette::fuzzy_score`; a hit re-focuses here (`presentable.rs:1126`). A reflexive toggle aims the inspector at its OWN view cell — inspect the inspector through the same dispatch. The inspector's focus and present-index are themselves a witnessed view cell, not a hidden Rust field.

## inspect-act
The INSPECT-ACT tab (`inspect_act_panel`, `cockpit.rs:3595`) is the Smalltalk inspect→act→inspect loop made real over dregg. It fuses reflection (`reflect.rs`) and cap-gated firing (`affordance.rs` + `world.rs`) into one surface: you see the messages the object understands, you send one, and the result is itself an inspectable object (`inspect_act.rs:1-38`).

What it shows: the focused cell's inspected state (the genuine `reflect_cell` `Inspectable`), then "messages understood" — the real `AffordanceSurface` projected for the viewer. Each message carries a real `dregg_turn::Effect` template and a **cap badge**: `you may send` (green) or `refused: insufficient authority` (red), decided by the proven `is_attenuation` lattice (`inspect_act.rs:75-90`). An unauthorized message is shown, never hidden (the anti-ghost stance).

How you use it: cycle the focus chip, read the messages, click "send" on an authorized one. The send routes through the real `AffordanceSurface::fire` → `AffordanceIntent::fire_through_world` → `World::commit_turn` — a REAL verified turn producing a real `TurnReceipt` — and the post-state re-inspects, closing the loop. A refused send surfaces in-band, never swallowed. The cockpit acts as the focused cell itself (the highest authority over its own window).

## graph
The GRAPH tab (`graph_panel`, `cockpit.rs:5757`) reflects the whole-image object-capability delegation graph. The desktop's thesis is "the View tree IS the ocap graph"; this projects the embedded `World`'s c-lists into a navigable multi-hop layout via `OcapGraph::build` (`graph.rs:1-39`).

What it shows: a count of cells (nodes) and capability edges, then the literal ocap graph — a directed edge `holder ──[rights]──▶ target` for every `CapabilityRef` in every cell's c-list, annotated `· delegated` (carries an R7 delegation epoch) and `· faceted` (effect-restricted). Below that is the MULTI-HOP layout: rooted on each *source* cell (no inbound edge — an authority origin), showing the transitive blast radius and laying out in delegation-depth layers, flagging any cycle.

How you use it: read the edges to see who holds what authority over whom; read the multi-hop layout to answer "what is the full blast radius of this cell's authority?" The reachability is the genuine transitive closure (`OcapGraph::reachable_from`), a true delegation depth. Every edge is a real `CapabilityRef` from the live ledger — an operator cannot be fooled about who can reach whom.

## web-of-cells
The WEB-OF-CELLS tab (`web_of_cells_panel`, `cockpit.rs:5952`) is the cockpit as a native browser of the `dregg://` docuverse. A `dregg://<cell>` link is a *capability into a cell*; "fetching" it is a verified, attested cross-cell read (a receipt plus a quorum-signed `AttestedRoot`).

What it shows: a "view as ROOT / view as EDITOR" toggle, then addressable cells as `dregg://` rows — each with its trusted-path origin chrome drawn from the LEDGER (never the page — the structural anti-phishing badge) and an `✓ attested` / `⚠ unattested` flag. Opening a cell reveals its per-viewer affordance surface ("you see N of M declared affordances — the rest are ATTENUATED away by your caps").

How you use it: toggle root/editor to watch the membrane reveal or attenuate affordances live; click a cell to open it; fire an affordance — which runs through this crate's embedded executor (`fire_affordance` lifts the projected web effect to `World::commit_turn`). The addressing is the genuine `WebOfCells`/`DreggUri`; the per-viewer rows are `AffordanceSurface::project_for` gated by `is_attenuation` (progressive enhancement → progressive attenuation).

## objects
The OBJECTS tab (`objects_panel`, `cockpit.rs:5714`) is the object browser organized around the protocol's accounting axes: cell lifecycle, turn proofs, and nullifiers. It is a direct reflection of the live `World` ledger and receipt log, no model of its own.

What it shows: a CELL LIFECYCLE column listing every cell with its lifecycle badge (`live`/`sealed`/`destroyed`, read from `cell.lifecycle`); then TURN PROOFS for recent receipts via `reflect::reflect_proof_status`; and under each receipt, its nullifiers via `reflect::reflect_nullifiers`.

How you use it: scan it to see the lifecycle posture of every object and the proof/nullifier state of recent turns. Nullifiers are the one-shot linearity record — a spend appears here as a nullifier under the receipt that consumed it, the same non-membership the circuit's note-spend gate enforces.

## proofs
The PROOFS tab (`proofs_panel`, `cockpit.rs:5898`) is the proof-attach and STARK verification-status board, surfaced as `ProofBoard::build(&world, 16)` (`proofs.rs:1-8`).

What it shows: a tally of three honest verification tiers, then per-turn entries tagged with the tier and an upgrade route. The tiers (`proofs.rs:55-67`): **Verified-by-construction** — the default in the embedded single-custody world; `commit_turn` runs the real verified executor inline, so the receipt's existence IS the proof. **Executor-signed** — the receipt carries the producer's Ed25519 signature over its hash. **STARK-attached** — an explicit succinct STARK over the whole-turn statement, so a light client verifies with NO trust in the producer.

How you use it: read it to know exactly what assurance a turn carries and what it would take to upgrade. The board never claims a higher tier than the receipt holds — and deliberately does NOT mint a multi-second STARK inside a panel build (that is the heavy `dregg_sdk::full_turn_proof` lane). This is the pale-ghost question answered honestly.

## lanes
The LANES tab (`lanes_panel`, `cockpit.rs:3870`) is the home of the moldable *gadgets* — interactive value-construction widgets that ride the proven `validate → predict → commit` spine. A `Gadget` (`presentable.rs:485`) builds a real protocol value with a live fail-closed `validate()`; a `CommittingGadget` adds `predict()` (simulate on a fork) and `commit()`, reusing `simulate.rs` verbatim.

The four gadgets: **predicate composer** — compose a caveat from real atoms; a vacuous or proof-strippable caveat is REFUSED. **turn builder** — build a call-forest, `predict()` its consequences in a fork. **attenuation dial** — pick a narrower rights tier; `build()` runs the real `is_attenuation`, refusing any tier that would AMPLIFY. **token loop** — mint → attenuate → delegate → discharge through the real cipherclerk macaroon crypto.

How you use it: pick a lane, construct a value, read the live fail-closed verdict. Gadgets are the L2/L3 interactive faces of the L1 presentation spine; their checks are the genuine protocol checks, and a committing gadget's `commit` is the identical turn its prediction previewed.

## powerbox
The POWERBOX tab (`powerbox_panel`, `cockpit.rs:6826`) is CapDesk — the trusted designation flow. An ocap system has no ambient authority: a confined app-cell holds exactly the caps in its c-list. The powerbox is the "open-file-dialog as grant ceremony": the app *requests* a cap it lacks, the trusted UI (the cockpit, NOT the app) presents a picker of what the USER holds, the user designates one, and the trusted UI mints a fresh attenuated cap into the app's c-list via a real grant turn (`powerbox.rs:1-13`).

How you use it: optionally launch a fresh confined app (it holds nothing — it can only ask), cycle the confer tier, then click a target to designate it. The app never sees the namespace; it gets precisely what you pointed at, narrowed. Three proven facts made tangible: the trusted UI holds no ambient authority of its own; the grant is strictly attenuating (`granted ⊆ held`, the anti-ghost tooth); and the mint is a real verified turn (the executor's no-amplification rule is the second gate).

## links-here
The LINKS-HERE tab (`links_here_panel`, `cockpit.rs:6564`) renders Ted Nelson's two-way link, navigable. The web-of-cells browser renders the *forward* link (a cell transcludes another); this renders it the OTHER way: *who transcludes / observes ME* — the genuine `Backlinks` witness-graph, projected through the focused agent's membrane (`links_here.rs:1-23`).

What it shows: a "view as SIGNATURE (fog the gated links)" ⇄ "view as ROOT (reveal all)" toggle and a depth cycle (1→2→3 hops). Each backlink carries its cited receipt and content commitment — a *verifiable fact* ("observer O quoted source S's value V at receipt R"), never a dangling pointer.

How you use it: read who quotes the focused cell, flip the authority toggle to watch a gated backlink reveal or fog (the fog-of-war for links, made tangible), cycle the depth, click a backlink to walk the docuverse backwards. The god's-eye link count versus the per-viewer count is shown, so the fog is visible: a viewer always sees ≤ the god's-eye map. The projection is the real `Membrane::project` gated by `is_attenuation`.

## organs
The ORGANS tab (`organs_panel`, `cockpit.rs:5843`) reflects each dregg *organ*'s live cell-state. Organs are dregg's higher-order primitives — cells whose installed program enforces a quantitative invariant: a trustline (`drawn ≤ ceiling` forever), a flash well (the net-floor flash-loan invariant), a channel, a mailbox, a court. Surveyed via `OrganSurvey::build` (`organs.rs:1-11`).

The honest split (`organs.rs:13-39`): trustline and flash well are *embed-core* — their entire enforcement is the cell's executor-installed program, re-evaluated on every touching turn, so their position is fully readable from the embedded ledger, decoded from the published blueprint slot constants. Channel, mailbox, and court are *node-service* organs whose full operation lives behind `captp`, which the headless build deliberately does not link — so they are shown as remote-path, NOT faked local state.

How you use it: read the live organs to see real bilateral-credit and flash-loan positions decoded off the ledger, and read the remote-path section to know honestly which organs need a connected node. This is the matrix row made real — trustline/flashwell enforced in embed-core (the cell program IS the invariant), channel/mailbox/court behind the network surface.
