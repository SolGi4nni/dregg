## raw-fields

The `raw-fields` face is the mandatory floor of the moldable inspector. It is the `RawFields` variant of `PresentationKind` (`starbridge-v2/src/presentable.rs:58-59`), and its body is `PresentationBody::Fields(Inspectable)` (`starbridge-v2/src/presentable.rs:109-110`) — a flat field-tree projected verbatim from `reflect.rs`. Every other face is optional; this one is not. The `Presentable` trait carries a blanket invariant that `RawFields` is ALWAYS the first element of any object's presentation set (`presentable.rs:336-346`).

The object data it shows is the existing `Inspectable`: a `title`, a `subtitle`, and a list of `Field`s, each a key/value pair read off a live protocol object. For a cell, `ReflectedCell::present` builds it by calling `reflect::reflect_cell` directly (`presentable.rs:658-665`) — no parallel schema, no re-encoding.

It exists to guarantee universal coverage. Making `RawFields` mandatory means every type — even one with no richer view yet written — has at minimum its `reflect_*` field-tree. "None" in the coverage matrix therefore means "no presentation richer than `RawFields`," never "uninspectable."

## graph

The `graph` face is the node/edge view — `PresentationKind::Graph` (`presentable.rs:60-61`), carried by `PresentationBody::Graph(GraphView)`. A `GraphView` is `nodes`, directed `edges`, and an optional `focus` cell (`presentable.rs:186-194`). Critically, the nodes and edges are the genuine `graph.rs` primitives read off the live ledger — never a parallel node model.

The object data it shows is any relation structure: the ocap web (who holds a capability reaching whom), an effect DAG, a Merkle tree, an attenuation lineage. For a cell, `cell_ocap_view` (`presentable.rs:792-815`) runs `OcapGraph::build(world)` over the whole image, then restricts to the edges that touch this cell.

It exists because the protocol is fundamentally a graph of authority and causation, and a field-tree cannot show reachability. The `graph` face answers "what does this object connect to, and how."

## domain-visual

The `domain-visual` face is the catch-all for domain-specific renderings — `PresentationKind::DomainVisual` (`presentable.rs:62-63`). It is backed by several bodies, each a different picture: `StateMachine`, `Gauge`, `Timeline`, `Lattice`, `MerkleTree`, `Trace` (`presentable.rs:112-124`).

The object data it shows is whatever the object's domain shape is: a cell's lifecycle as a state machine, an issuer well's signed balance as a gauge, a finality ladder. For a cell, `lifecycle_state_machine` (`presentable.rs:820-845`) builds a `StateMachineView` from the real `CellLifecycle` — the five canonical states (Live/Sealed/Destroyed/Migrated/Archived) and the verb transitions between them.

It exists because some objects have a natural picture that neither a field-tree nor a generic graph captures. This face is where the inspector becomes legible to a domain reader: you SEE the cell is Sealed, sitting on the diagram.

## affordances

The `affordances` face is "the messages this object understands" — `PresentationKind::Affordances` (`presentable.rs:64`). It re-houses the genuine `InspectAct` `Message` list (`presentable.rs:667-692`). For a cell, it derives the viewer's authority with `viewer_authority_over`, calls `InspectAct::build`, and packages the messages via `messages_as_inspectable`.

The object data it shows is the list of verbs the object can receive, each annotated with its required rights and a cap badge: `"{effect} · requires {required} · {you may send | refused}"` (`presentable.rs:746-757`).

It exists, and divides per viewer, because authority is not uniform. The same cell shows a different affordance set to its owner than to a stranger, since the viewer's held rights are computed off the live c-list. This is what makes the inspector a place you act FROM, not just read.

## provenance

The `provenance` face is the time-travel / receipt-chain / lineage view — `PresentationKind::Provenance` (`presentable.rs:66`), carried by `PresentationBody::Timeline(TimelineView)`. A `TimelineView` is an ordered list of `TimelineEvent`s, each a monotone key `at`, a `label`, and an optional navigable `hash`.

The object data it shows is the object's history off the live receipt log. For a cell, `cell_provenance` (`presentable.rs:769-787`) walks `world.receipts()`, filters to the receipts this cell authored, and emits one event per receipt in commit order, each carrying the receipt hash, action count, and computrons used.

It exists because a turn leaves a verifiable receipt, and the receipt chain IS the object's lineage. This face is the History scrubber — and because each event anchors on a real hash, it is also the seam to time-travel.

## invariant

The `invariant` face is the conservation / commitment-binding / cost readout — `PresentationKind::Invariant` (`presentable.rs:68-69`). It shows not what an object IS but what it must always SATISFY: that balances conserve (Σδ=0), that a value is bound into the published commitment, that authority does not amplify. It draws on `Gauge`, `MerkleTree`, and `Trace` bodies.

The object data it shows is the live readout of a protocol invariant: a `GaugeView`'s value against its ceiling, a `MerkleTreeView`'s leaves/root/path where the verifier gadgets recompute against the real machinery.

It exists because dregg's safety IS its invariants. This face is where you watch the property hold — and, paired with a verifier `Gadget`, where you can re-run the check live and get green or red against genuine cryptographic machinery.

## source

The `source` face is the program / constraint-set / Datalog "what-is" text the object enforces — `PresentationKind::Source` (`presentable.rs:70-71`), carried by `PresentationBody::Prose(String)`. It is the only face whose body is plain text: the rendered program a cell runs, the predicate tree a constraint denotes, the Datalog derivation a biscuit authorizes.

The object data it shows is the object's defining text — the rule, not the runtime value. Where `raw-fields` shows a constraint's current binding, `source` shows the constraint's source.

It exists because a protocol object is frequently a small program — a predicate, a caveat chain, a factory descriptor — and you cannot understand its behavior from its fields alone; you must read what it enforces. This is the "what-is" teaching face.

## framework

The framework is the moldable inspector itself: the idea, taken from Pharo's `gtViewsFor:`, that one object offers a SET of named lenses rather than a single fixed view, and that the inspector can turn that lens on anything — including itself. The existing `reflect.rs` `Inspectable` becomes the mandatory `RawFields` body, and the other six faces register beside it (`presentable.rs:1-36`). Everything is pure data projected from the live `World`; no gpui type crosses the boundary.

Four pieces carry it. `Presentable` (`presentable.rs:341-346`) is THE trait — an object's `present(ctx)` builds its full set fresh off the live world. The `Registry` (`presentable.rs:901-995`) resolves a `FocusTarget` to the right newtype `Presentable` and its `Halo` ring; new object kinds add one arm. `Spotter` (`presentable.rs:1122-1186`) is universal search — it indexes every live object's every presentation by `search_text` and ranks with `palette::fuzzy_score`. `Halo` (`presentable.rs:593-622`) is the per-object direct-manipulation ring: the universal three (Inspect/Grab/Explain) on every object, extended per `ObjectKind`.

It exists so that "every object is inspectable, and the inspector inspects itself" is literally true. The `FocusTarget` enum carries a `ViewCell` arm — the inspector's own camera-aim, self-hosted as a real cell — and `DebugFrame`/`World`/`Cockpit` arms, all resolving through the SAME `present()` dispatch (`presentable.rs:854-881`). "Debug the debugger" is just this dispatch at a higher level. The reflexive cycle is broken by a unit delay: the registry reconstructs a `ViewCell` from its witnessed prior-frame state on the ledger.
