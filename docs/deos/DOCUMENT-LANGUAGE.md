# THE DREGGVERSE DOCUMENT LANGUAGE
## A patch-theoretic hypermedia authoring layer riding the cell substrate — Nelson's Xanadu and Engelbart's NLS, made witnessed and cap-secure, with conflicts as first-class states

*A teacher's-and-architect's treatment. The math first (Pijul-shaped, intuition then
rigor), then the dregg realization, then the implementation shape. Citations to prior art
are gathered and HONESTLY flagged where they come from memory. The companion docs are
`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` (the patch-theory ≅ event-structure calibration),
`BRANCH-AND-STITCH-PROTOCOL.md` (stitch = pushout), and `INSPECTOR-FRAMEWORK.md` (the
Presentable/cell substrate this rides).*

---

## 0. THE ONE-SENTENCE ANSWER

> **A dregg hypermedia document is a patch-theoretic object riding the cell substrate: a
> document is a cell (or cell-subgraph), an edit is a patch is a turn, the document's
> *content* is the result of applying its patch-history, transclusion is a verified
> cross-cell quote, two-way links are the witness-graph read backward — and a conflicted
> region is a first-class STATE you resolve with a later patch, never a rejected merge.**

The calibration (settled, in `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §0 and the
`distributed-houyhnhnm-frontier` memory) is that patch theory — Darcs → Pijul, with
Mimram–Di Giusto's categorical reading (merge = **pushout**, conflicts as **first-class
objects**) — is the *same mathematical object* as the event-structure + RCCS + sheaf-gluing
construction the dregg turn/blocklace layer already instantiates. Patches-commute is
Mazurkiewicz independence is the blocklace's causal order; inverse-patches is RCCS
reversibility; merge-as-pushout is sheaf gluing. So **the turn layer already *is* a patch
algebra** — "turns as patches" is not a re-foundation. Patch theory's genuinely-new value
is concentrated in two forward faces, and this document is about the first:

- **(a) conflicts-as-first-class-objects → THE DOCUMENT LANGUAGE.** This is Pijul's native
  home, and the part the dregg substrate does *not* yet have: a conflicted document is a
  valid sub-state with two live alternatives, resolved by a later patch — not a merge
  failure. This doc designs it.
- **(b) merge-as-pushout → the stitch correctness criterion.** Already its own doc
  (`BRANCH-AND-STITCH-PROTOCOL.md` §3): a stitch is a morphism into the colimit; patch
  theory tells us whether we built it right. We *connect* to it (§5), we do not re-derive
  it here.

The honest state, stated up front so the rest reads against it: **the hypermedia
substance is built** on two sides. The Nelson/Engelbart side: `deos-web-cells`'s
`DreggverseDocument` (an ordered list of spans, own-content interleaved with byte-range
transclusions, resolved per-viewer through the membrane), the verified `TranscludedField`,
the two-way `Backlinks`, the per-viewer `Membrane`, the `Rehydration` liveness-type. The
*Pijul-shaped patch core* side: the **`dregg-doc` crate** — a document as a graph of atoms
with alive/dead status, edits as graph operations (`Add`/`Delete`/`Connect`/`SetField`),
history as a fold of composable patches, and **conflicts as first-class states**. The two
sides ride one substrate; `dregg-doc` is the patch layer, and `DreggverseDocument` remains
*content-flat* (it is the rendered result, with no patch history of its own — `dregg-doc` is
the layer that produces such a rendering). The patch core rides — does not replace —
everything on the Nelson/Engelbart side.

---

## 1. THE THESIS — WHAT A DREGG HYPERMEDIA DOCUMENT *IS*

### 1.1 The four identifications

A dregg document is built from four identifications, each of which is *already a thing dregg
has*, so the document language is a naming-and-welding act, not a from-scratch build:

| document notion | dregg object | already built? |
|---|---|---|
| **a document** | a **cell** (or a connected cell-subgraph), content-addressed, cap-gated | yes — `dregg_cell::Cell` |
| **an edit** | a **patch** = a **turn** (an effect over the document cell, leaving a receipt) | yes — the turn/effect/receipt spine; the *patch grammar* is `dregg_doc::Patch` (`Add`/`Delete`/`Connect`/`SetField`) |
| **the document's content** | the result of **applying the patch-history** (fold the turns from genesis) | yes — `dregg_doc::History::replay`/`replay_to`; content-as-patch-fold is `dregg_doc::content` |
| **transclusion** | a **verified cross-cell quote** (`TranscludedField` — content-addressed + receipt + quorum) | yes — `starbridge-web-surface/src/transclusion.rs` |
| **a two-way link** | the **witness-graph read backward** (`Backlinks` / `DreggverseMap`) | yes — `links_here.rs`, `dreggverse_map.rs` |

The thesis in one line: **a document is a cell whose state is the fold of its edit-patches,
its quotes are verified cross-cell reads, and its inbound links are the witness-graph — so
every property the cell substrate proves (cap-gating, attestation, conservation, no-amp,
per-viewer projection) is a property the document inherits for free.**

### 1.2 Nelson and Engelbart, made witnessed and cap-secure

The two ancestors and what dregg adds to each:

- **Ted Nelson's Xanadu** (1965–; *Literary Machines*, 1981) wanted **transclusion**
  (include-by-reference, the quoted material keeping its identity and provenance — same
  bytes, same source, visibly cited, never copy-and-cut) and **two-way links** (navigable
  both ways, never dangling). Xanadu could never make either honest: in an
  ambient-authority world a "transcluded" quote is just a copy (nothing forces it to equal
  the source, nothing stops it rotting when the source moves, nothing bounds the authority a
  quote confers), and the back-link was a hand-maintained index that drifts. dregg ships the
  missing piece — **the verified cross-cell finalized read** (`TranscludedField::include`:
  the bytes are content-addressed AND carry a receipt + a quorum-signed `AttestedRoot`, so a
  quote *is* the value the source committed at a cited, immutable receipt; a forge cannot be
  cited; `Backlinks` renders the other direction as a *fact*, not a pointer). The Nelson
  pieces are *built* (`starbridge-web-surface/src/transclusion.rs`,
  `starbridge-v2/src/web_cells.rs`, `links_here.rs`).

- **Doug Engelbart's NLS / oN-Line System** (1968, the "Mother of All Demos") wanted live
  collaborative structured editing, view-control (the same document seen many ways), and
  inter-linked statements with stable addresses. dregg's contribution is that the *liveness*
  and the *view-control* are not application conveniences but **substrate facts**: the
  Presentable framework (`INSPECTOR-FRAMEWORK.md`) gives a document multiple named
  presentations (rendered / source / patch-history / conflict-view) the way Pharo gives an
  object multiple views; collaborative editing is the membrane (per-viewer projection) plus
  joint-turns (co-commit); and every statement has a stable content-addressed identity
  because it is a node in a cell.

What is *new beyond both*: the document is **patch-theoretic** (its content is a history of
composable, invertible, mergeable patches) and **conflict-tolerant** (a disagreement is a
state, not an error) — and all of it is **light-client-unfoolable** (the same replay tooth
that protects a turn protects a document edit; `AssuranceCase.lean::unfoolability_guarantee`).

---

## 2. THE NATIVE MATH — PIJUL-SHAPED, TAUGHT

### 2.1 The categorical foundation (Mimram–Di Giusto): repositories, patches, pushout

**Intuition.** Forget "a repository is a sequence of commits." Think instead: a **repository
is a state**, and a **patch is a labelled, directed way of getting from one state to
another**. If states are objects and patches are morphisms, a repository's history is a path
through a category. The single deep idea is what *merge* is.

**The formal object.** Mimram–Di Giusto, *A Categorical Theory of Patches* (MSCS / arXiv,
~2013 — *date from memory, confirm*), models patches as the morphisms of a category **P**
whose objects are repository states. Two patches `f : A → B` and `g : A → C` made *from the
same starting state* `A` (a fork) are merged by taking their **pushout**: the object `D`
together with patches `f' : C → D` and `g' : B → D` such that `g' ∘ f = f' ∘ g`, and `D` is
*universal* (initial) among all such cocones. In plain terms: `D` is "the smallest state
that contains the effect of both edits, identifying exactly what the two edits forced to be
identified, and nothing more."

```
        f
   A ───────▶ B
   │          │
 g │          │ g'        D = pushout(f, g) = the merge
   ▼          ▼
   C ───────▶ D
        f'
```

**Why the pushout makes merge associative, commutative, and (where it exists) always-defined.**
These are not lucky facts about an implementation; they are the *universal property* doing
the work:

- **Commutative.** The pushout of `(f, g)` and of `(g, f)` are the same object up to unique
  isomorphism — the universal property is symmetric in the two legs. So `merge(p, q) =
  merge(q, p)` by construction. Order of application of two concurrent edits cannot matter.
- **Associative.** Merging three forks pairwise in any grouping yields the same colimit (a
  finite colimit is the colimit of the whole diagram, however you bracket it). So
  `merge(merge(p, q), r) = merge(p, merge(q, r))`.
- **Always-defined (the catch, and Pijul's fix).** A pushout need not exist in an arbitrary
  category — and Mimram–Di Giusto's first model is exactly where it *fails*: in the naive
  category of "files as sequences of lines," some forks have no pushout (two inserts at the
  same position have no canonical merged order). Their resolution — and Pijul's — is to
  **change the category so the pushout always exists**: enrich states from sequences to
  *graphs* (free objects in a richer category), where the colimit is just the union of
  graphs and the missing order becomes an explicit, representable structure (§2.2). **The
  conflict is not the absence of a merge; it is the *shape of the merged object*.** That
  single move is the whole reason conflicts can be first-class.

This is the *exact same* universality the dregg side already leans on: `LaceMerge.lean`
proves the blocklace merge is a `Finset`-union join (commutative/associative/idempotent/
monotone) — the colimit of the configuration diagram (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`
§3.1). The patch-theory pushout and the blocklace join are the same colimit seen in two
notations.

### 2.2 Pijul's concrete data model: a document as a graph of alive/dead nodes

**Intuition.** Pijul (the production version-control system built on this theory; Pierre-Étienne
Meunier et al., ~2017– — *date from memory*) makes the abstract pushout concrete. A document
is **not** a string of lines; it is a **directed graph** whose vertices are *byte intervals*
(atoms of content — characters, lines, or arbitrary spans) and whose edges encode the
**order** "this atom comes before that one." Each vertex carries an **alive/dead** status.
The visible document is the result of a **topological walk** over the *alive* vertices
following the order-edges.

**Patches as graph operations.** Every edit is one of a tiny set of graph operations:

- **add** a new vertex (a span of content) — a fresh atom with a unique, content-derived id;
- **delete** a vertex — *not removal* but flipping its status to **dead** (a "deletion edge"
  marks it tombstoned). Nothing is ever physically lost; deletion is monotone (you add a
  tombstone), which is what makes deletes commute with everything;
- **connect** — add order-edges between vertices (e.g. "the new atom goes after X and before
  Y"), wiring a fresh atom into the order.

Because every operation is *additive* (add a vertex, add a tombstone, add an edge), patches
**commute** whenever they touch disjoint parts of the graph, and **applying a patch is
idempotent and order-independent** up to the partial order on patches. The graph at any
moment is the union of all applied patches' vertices and edges — *the colimit, computed by
union*. That is precisely why the merge "always exists": you never have to *decide* an order
to take the union; you only have to *display* it.

**The pseudo-graph that makes merges always-defined.** When two patches each insert an atom
"after X" with no edge between the two new atoms, the union graph has **two vertices with no
order between them** — a genuine *antichain* in the order. Pijul represents this directly:
the merged graph simply *contains both, unordered*. There is no failure. The walk that
renders the document now hits a fork in the graph with two live successors and no edge to
choose between them — and **that fork is the conflict** (§2.3). Pijul calls the structure
that holds the unresolved order a *pseudo-graph*; the point is that the data model has a
faithful representation of "we both edited here and the order is undecided," so the merge is
total.

**The dregg fit.** This graph-of-alive/dead-atoms model is *already congenial* to the
substrate. A document cell's content is a `HeapRoot` / field structure (a Merkleized map);
vertices are content-addressed atoms (the same content-addressing the whole system uses);
"alive/dead" is a monotone tombstone (the same shape as the nullifier set and the
revocation tombstone tree, `INSPECTOR-FRAMEWORK.md` slices 4/7); and the union-merge is the
I-confluent fragment (§2.4). The Pijul graph is realized as `dregg_doc::DocGraph`, and every
primitive it needs (content-addressed atoms, monotone tombstones, Merkle commitment,
union-merge) is one the substrate already ships (the `substrate`-feature ride binds them).

### 2.3 Conflicts as FIRST-CLASS STATES

This is the heart, and the genuinely-new contribution to the dregg document layer.

**Intuition.** In Git, a merge conflict is a *failure mode*: the merge stops, spits conflict
markers into the file, and refuses to complete until a human edits them away. The conflict is
*outside* the model — it lives in `<<<<<<<`/`>>>>>>>` text the tools don't understand. In
Pijul, a conflict is a **valid state of the document**: the merged graph genuinely *has* two
live, mutually-unordered alternatives at a region, and that graph is a first-class object you
can store, share, branch from, and — crucially — **resolve later, with another patch**. A
resolution is *just another edit*: a patch that adds the order-edges (or the tombstones) that
collapse the antichain to a single live walk. Resolution is monotone and composes like any
patch; it is not a special "finish the merge" operation outside the algebra.

**Why this matters for a *document* specifically.** A document is the one place where "leave
the disagreement *in* the artifact and resolve it when you understand it" is the *right*
semantics, not a workaround. Two co-authors edit the same paragraph; the merged document is
*honestly conflicted there* and *clean everywhere else*; the conflicted region renders as
"here are both versions, choose or rewrite" — and the rest of the document is fully usable
*while the conflict stands*. You do not block the whole document on one contested paragraph.
This is exactly the `BRANCH-AND-STITCH-PROTOCOL.md` insight ("explorations are never wasted;
cherry-pick the insight out of a failed experiment") applied at the granularity of a
paragraph instead of a whole branch.

**The formal shape.** A conflicted region is a sub-graph that is an **antichain in the order
relation**: a set of live vertices `{v₁, …, vₙ}` reachable at the same position with no
order-edge among them. The document's renderer, walking the graph, reaches a vertex with
multiple un-ordered live successors and *must* present them as alternatives (it cannot
linearize them, because the order genuinely is not in the graph). A **resolution patch** adds
order-edges and/or tombstones that turn the antichain into a chain (or kills all-but-one),
restoring a unique walk. Because resolution is additive, two people can even *concurrently
propose different resolutions* — yielding a (smaller) conflict among the resolutions, which
is again a state, resolved again by a later patch. The model is closed under its own conflicts.

**The dregg realization of conflict.** dregg already has a *cryptographic* conflict relation
in the value layer (double-spend = a nullifier collision = two branches whose union is not a
configuration; `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §3.6). The document conflict is the
*data-level* sibling: a content antichain. The crucial dregg refinement is the **two regimes**
(§2.4): a conflict in the *monotone* (I-confluent) fragment of a document never even arises
(the union is unconditionally a valid state); a conflict only becomes a *resolve-required*
state where a non-monotone document invariant is in play (a document that pins an authority,
a conservation, or an explicit single-valued field). So dregg can tell you, structurally,
*which* conflicts are real (need a human/consensus decision) and which are illusory (the
classifier merges them clean).

### 2.4 Mapping onto dregg: the I-confluent fragment vs. the conflict-bearing fragment

The whole map of §2 onto the substrate is the *two-regime* split, which dregg has already
proved (`Confluence.lean`, the `rhizomatic-dregg-slotting` memory):

- **The clean-merge part = the I-confluent / rhizomatic fragment.** Grow-only content,
  append-only spans, monotone tombstones — `IConfluent I := ∀ x y, I x → I y → I(x ⊔ y)`.
  Two branches over an I-confluent document *always* glue by union; the merge is the colimit,
  no conflict possible (the sheaf is literally a sheaf there — gluing always succeeds). This
  is exactly the Pijul union-of-graphs merge, and it is the *common case* for prose: most
  concurrent edits touch disjoint spans and merge silently. Rhizomatic (`~/dev/rhizomatic`,
  the Merkle-CRDT G-Set fragment) *is* this fragment taken globally — its 8-operator algebra
  (`select·union·mask·group·expand·prune·resolve·fix`) is a ready-made query/merge face for
  the document's monotone layer, and its `resolve` operator is *exactly* the per-reader
  conflict-resolution-at-read-time that a document's conflict-view needs.

- **The conflict-becomes-a-state part = conservation/authority.** Where a document carries a
  *non-monotone invariant* — a single canonical title field, a conserved quantity, a pinned
  authority — two branches' union may violate it, and `Confluence.lean`'s
  `nonpairwise_escalation` *constructs* the clashing pair. Here the merge does not silently
  union; it produces a **first-class conflict state** (the antichain) that a resolution
  patch — possibly requiring a joint-turn or a settlement decision — must collapse. The
  `ConfluenceClassifier` is the static gate that decides, per region, which regime applies:
  it is the precise tool that answers "is this a real conflict or an illusory one." This is
  the document-language reading of the same wall that forces consensus in the value layer.

So the native math is: **Pijul's graph-of-atoms + always-total union merge for the monotone
fragment, with conflicts surfacing as first-class antichain states exactly at the
non-monotone (conservation/authority) boundary the `ConfluenceClassifier` already draws.**

---

## 3. COLLABORATIVE EDITING ON DREGG

Multiple authors editing one document is the composition of four things dregg already has,
plus the patch grammar of §2. Nothing here is a new distributed-systems mechanism; it is the
document-shaped reading of the branch-and-stitch protocol.

### 3.1 An author's draft is a branch; publishing is a stitch (pushout)

Each author edits in their own **branch** of the document — a divergent configuration off a
past cursor, *free and confined* exactly as `BRANCH-AND-STITCH-PROTOCOL.md` §1–2 describe.
The draft holds **no cap to the shared document** (firmament confinement), so a draft edit
*cannot leak* into the published document; its side-effects are structurally imaginary until
published. The branch's **liveness-type is honestly `Virtual/Branch`** (the `Rehydration`
type, derived not hand-set, `rehydrate.rs`) — the system cannot lie about whether you are
reading the published document or someone's draft.

**Publishing = a stitch = a pushout into the shared document.** When an author publishes,
their branch's patches are merged into the shared document via the `Stitch` primitive
(`BRANCH-AND-STITCH-PROTOCOL.md` §3), which is the pushout of §2.1: the I-confluent spans
merge clean; a contested region yields a first-class conflict state in the shared document
(not a rejected publish); and any genuinely conserved/authority-pinned clash is the
linear-logic-forced *explicit drop* (you must say what you are dropping; you cannot lose a
co-author's paragraph by silent omission). The result is a turn the shared document cell's
gate admits — a real, witnessed publish, leaving a receipt.

### 3.2 The membrane: per-viewer projection of a document

Two readers of "the same" document do not see identical bytes — each sees the projection
their caps authorize. This is *already live* in the document layer:
`DreggverseDocument::resolve_for` (`deos-web-cells/src/document.rs`) resolves a document
**through the viewer's `Membrane`**, and a span whose source the viewer's fetch-allowlist
cannot reach renders **darkened** — its provenance (the citation) survives, its bytes
withheld, *never forged, never substituted* (`web_cells.rs` `DocumentSpanRow`, the
`build_document` weld; the proven recipe
`a_weaker_viewer_sees_darkened_spans_not_the_source_values`). The membrane meet is the real
`is_attenuation` lattice; the projection cannot amplify (`transclusion_no_amplify`). So
"who may read which region" is the same per-DOM-region cap machinery the rehydration layer
proves, lifted to *document regions*: a document is a frustum re-derived per viewer.

### 3.3 Cap-gated editing: who may edit which region

Read-projection (§3.2) is the membrane; *write*-authority is the affordance cap-gate.
`web_cells.rs` already publishes a document cell's surface as the canonical
`{view, comment, edit, admin}` affordance set on the three-tier rights chain
`Signature ⊂ Either ⊂ None`, each carrying a real `Effect` template the executor runs. Lift
this to **per-region** editing: a document is a cell-subgraph, and an edit-patch over a
region is an effect over the cell(s) that own that region — so "who may edit which region" is
"who holds the `edit` affordance cap reaching those cells." The per-DOM-region caps of
`DISTRIBUTED-SERVO.md` §2 (and the `SurfaceCapability` scoping in `rehydrate.rs`) *are* the
per-region edit caps; an edit a viewer is not cleared for is refused **in-band at the gate**
(the anti-ghost tooth, `WebCellsBrowser::fire_affordance`), before any turn — and a *granted*
region-edit can be conferred precisely and attenuably through the powerbox (the
`SemiReinteractiveTransclusion` upgrade is exactly this shape: a quote becomes an
attenuated interact only through a real powerbox grant).

### 3.4 Joint editing: co-commit and the cross-party stitch

When two authors must edit *atomically together* (a co-signed change — e.g. a contract clause
both must agree to), that is a **joint-turn** (`FamilyBinding`, the co-commit machinery
`BRANCH-AND-STITCH-PROTOCOL.md` §1). A **cross-party stitch** — merging one author's branch
into another's where the regions interleave — is a **partial turn with holes the consenting
parties fill** (the `partial-turn-promises` thread: the hole *is* the consent point, and a
promise-hole *is* a nullifier whose resolution is a spend — so one-shot linearity is the
double-spend non-membership the circuit already enforces). The semi-automated path: auto-merge
the I-confluent spans, surface only the genuine conflicts for the authors to drop-or-resolve.

### 3.5 How a conflict-as-state is presented and resolved in the inspector

A conflicted document gets a **`ConflictView` presentation** (a `DomainVisual` kind in the
Presentable framework, `INSPECTOR-FRAMEWORK.md` §1.1). It renders the antichain region as
its live alternatives side-by-side (each carrying its authoring branch + receipt provenance,
so "who wrote which alternative" is a *fact*), with the clean spans around it fully rendered.
Resolution is a **gadget** (`INSPECTOR-FRAMEWORK.md` §1.2): a `CommittingGadget` whose
`build()` produces the resolution patch (add the order-edges / tombstones that collapse the
antichain), whose `predict()` shows the resolved render *before* `commit()` runs the identical
turn (the `IntentDraft → simulate → commit` spine). Because resolution is just another
cap-gated edit-patch, only an author holding the region's `edit` cap may resolve it, and the
resolution leaves a receipt — the resolution itself is witnessed and revertible.

---

## 4. THE IMPLEMENTATION SHAPE

### 4.1 Where the patch core lives: the `dregg-doc` crate

The Pijul-shaped patch core lives in the **`dregg-doc` crate** (`dregg-doc/`, package
`dregg-doc` v0.1.0, edition 2024, AGPL-3.0). It is a small, `gpui`-free, `cargo test`-able
core, and by design its **own (empty) workspace** so the parent dregg workspace's build does
not pull it in — and so the default core is **dependency-free**: pure data structures and
algorithms, fast and testable in isolation ("let it breathe"). Its public modules:

- **`graph`** — `DocGraph`: a keyed atom map `BTreeMap<AtomId, Atom>` + order-edges
  `BTreeMap<AtomId, BTreeSet<AtomId>>` + a single-valued field store
  `BTreeMap<String, Vec<FieldAssign>>`. This *is* the Pijul graph (atoms with alive/dead
  status, edges = the order relation, plus the non-monotone field fragment).
- **`atom`** — `Atom` (id, content, `Status::{Alive,Dead}` with the monotone "Dead wins"
  `Status::join`, `Provenance{author,patch}`); `AtomId::derive` (content-addressed).
- **`patch`** — the `Op` grammar `Add{id,content,after}` / `Delete{id}` (tombstone) /
  `Connect{from,to}` / `SetField{name,value,superseding}`, with the inverse ops
  `Resurrect`/`Disconnect`/`RetractField`; `Patch{author,ops}` with a content-addressed
  `id()`, `apply`/`apply_to`, `compose`, and `invert` (RCCS reversibility).
- **`merge`** — `merge`/`merge_all`: the total, commutative, associative, idempotent union
  (the pushout/LUB), via the pointwise `Status::join` + edge/field set-union of
  `union_in_place`.
- **`history`** — `History`: `commit`, `replay`/`replay_to` (time-travel), `branch` (fork a
  draft), `stitch` (publish = the pushout merge of two folds).
- **`content`** — the linearization: `content` walks the alive atoms, surfacing a fork as a
  first-class `ConflictRegion` (`Segment::{Clean,Conflict}`, an antichain of ≥2 live
  `Alternative`s, each carrying provenance); `walk_atoms` is the per-atom companion.
- **`regime`** — `Regime::{Prose,Field}`, the per-region monotone-vs-real classifier
  (`needs_consensus`).
- **`resolve`** — resolution is just another authored patch: `resolve_connect` /
  `resolve_keep` / `resolve_keep_in` (drops a dropped branch *whole*) / `resolve_field`.
- **`resolution`** — `resolutions`/`resolutions_for`: the one-click resolution menu
  (`Resolution::{Keep,Order,ChooseField}`, each a ready authored `Patch`) — the model that
  makes a rendered conflict resolvable from the surface.
- **`doc`** — the ergonomic authoring path: `Doc`/`Granularity::{Line,Word}`, an LCS-diff
  `edit` that mints predecessor-seeded stable atom ids (so duplicate tokens stay distinct).
- **`depend`** — the theory of patches: `dependencies`/`transitive_dependencies`/
  `dependents`/`commute`/`unrecord`/`cherry_pick`.
- **`blame`** (`blame`/`blame_summary` — attribution that survives moves), **`threeway`**
  (`three_way`/`merge_base`/`render_three_way` — diff3), **`composition`** (`Op::Embed`,
  composed documents), **`literate`** (the `<<< … >>>` conflict markup parse/render),
  **`commit`** (`Commitment`/`commit` — the in-crate `DefaultHasher` stand-in commitment).

  The default core stays **standalone and dependency-free**; the *ride* onto the live
  substrate is behind off-by-default features:

  - **`substrate`** welds onto the real `dregg-cell` + `dregg-turn`: `to_heap_map` projects a
    `DocGraph` into a real `(collection_id, key) -> 32-byte` cell heap and `substrate_commit`
    is the **sorted-Poseidon2 real heap root** over it (replacing the `commit` `DefaultHasher`
    stand-in with the faithful commitment a light client trusts); `executor_drive::
    ExecutorDrivenDoc` desugars an edit into genuine `Effect::SetField` writes driven through
    the real `TurnExecutor` (cap-gated, finalized, leaving a `TurnReceipt` that *is* the
    provenance); `desktop::DesktopSurface` projects a cockpit workspace as a document.
  - **`rope`** welds a `ropey::Rope` editor buffer onto the patch core (`RopeDoc`,
    `rope.rs`), pinned to deos-zed's exact `ropey` version so its real `Editor` buffer plugs
    in at the seam.

  So the substrate ride is *built but optional*: a `DocGraph` projects onto a `HeapRoot`-shaped
  content map of a document cell (atoms are heap leaves, content-addressed, Merkle-committed);
  a `Patch`'s effects are real turns writing those leaves + tombstones; the document's
  *content* is `History::replay_to(tip)` folded through the patch grammar; `merge` is the
  I-confluent union for the monotone fragment and a `Conflict` state at the non-monotone
  field boundary. The wiring of `Regime` to the live `ConfluenceClassifier` per region is the
  one still-forward weld (§4.4).

- **`document` module in `starbridge-v2` (the native gpui editor face).** Beside
  `web_cells.rs` / `links_here.rs`: the gpui-free MODEL of a document view (rendered spans,
  conflict regions, patch-history) that the native cockpit renders — exactly the pattern
  `web_cells.rs` already follows (a `cargo test`-able text model, gpui renders it). This is
  where `DreggverseDocumentView` (already built) grows a patch-history and conflict-view
  face.

- **`deos-leptos` (the reactive web editor face).** The Leptos crate already proves
  *cell-state = `RwSignal`* and *affordance-fire = a real verified turn through the executor*
  (`deos-leptos/src/lib.rs`, the three mappings; the seam is closed — a real
  `TurnExecutor`, no mock). The document editor's web home is here: the document's content is
  a `Memo` over the patch-history signal; an edit POSTs a patch-turn through
  `server::fire_affordance`; the committed state re-seeds the signal and the view reacts. A
  conflict region is a reactive island whose alternatives are signals; resolution is an
  affordance-fire. SSR-render → per-island-hydrate *is* the per-viewer membrane projection
  (`parallel_source_view.rs` / `transclusion_demo.rs` are the seeds of the source-vs-rendered
  document views).

**The deos desktop already edits documents through `dregg-doc`.** The cockpit's document
editor (`starbridge-v2/src/deos_desktop/mod.rs`) holds a live `dregg_doc::Doc`: a document is
a cell, and typing diffs the buffer into a `dregg_doc::Patch` whose provenance flows into
blame. The same `dregg_doc::{Author, Doc, Granularity}` path backs the deos-zed editor face
(`deos-zed`'s `Editor` / `cell_git.rs`, where `dregg_doc::blame` gives move-stable blame) and
the deos-js composer (`dregg_doc::composition`'s `Op::Embed` embed algebra). So the patch core
is not a model awaiting a consumer — it is the document layer the live surfaces already run on.

### 4.2 What is reused vs. genuinely new

**Reused (built, leaned on, not reinvented):**

| piece | crate / file | role in the document language |
|---|---|---|
| `DreggverseDocument` / `Span` / `resolve_for` | `deos-web-cells/src/document.rs` | the content-flat EDL: own + byte-range-transclusion spans, per-viewer resolve. The patch core *produces* this as its rendered output. |
| `TranscludedField` (verified quote) | `starbridge-web-surface/src/transclusion.rs` | transclusion = a verified cross-cell finalized read; the quote IS the source's committed value. |
| `Backlinks` / `DreggverseMap` | `transclusion.rs`, `links_here.rs`, `dreggverse_map.rs` | two-way links = the witness-graph read backward, per-viewer-fogged, navigable. |
| `Membrane` / `Rehydration` | `starbridge-web-surface/src/rehydrate.rs` | per-viewer projection + the draft-vs-published liveness-type. |
| `AffordanceSurface` + powerbox | `web_cells.rs` | per-region edit caps; the `{view,comment,edit,admin}` gate; attenuated region-grants. |
| the turn/effect/receipt spine + `simulate`/`commit` | `dregg-turn`, `starbridge-v2/src/simulate.rs` | a patch IS a turn; predict-then-commit for every edit/resolution gadget. |
| `LaceMerge.lean` / `Confluence.lean` / `ConfluenceClassifier` | `metatheory/`, the classifier | the union-merge join (colimit) + the monotone-vs-conflict regime gate. |
| rhizomatic's 8-op algebra (`select…resolve…fix`) | `~/dev/rhizomatic` | a ready-made query/merge/`resolve` face for the monotone document fragment. |
| Presentable / Gadget framework | `INSPECTOR-FRAMEWORK.md` (to build) | a document's rendered/source/patch-history/conflict presentations; edit/resolve gadgets. |

**The `dregg-doc` patch core (BUILT — the structural layer the rest welds onto):**

1. **The Pijul-shaped patch graph** — `DocGraph`, alive/dead atoms, order-edges + the
   single-valued field store; the data model that makes merges total and conflicts
   representable. *(`DreggverseDocument` stays content-flat; this is the patch layer that
   produces a rendering.)*
2. **The patch grammar + algebra** — `Patch` = `Add`/`Delete`/`Connect`/`SetField`; `apply`,
   `compose`, `invert`, `merge` (= the LUB/union the pushout computes).
3. **Conflicts-as-first-class-states** — the `ConflictRegion` antichain state + `resolve_*`,
   and `resolutions`/`resolutions_for` (the one-click resolution menu). *(The `ConflictView`
   presentation + resolution gadget as moldable-inspector surfaces is the forward UI weld.)*
4. **The patch-history fold = document content** — content as `History::replay`/`replay_to`
   over the patch grammar, with provenance carried per atom (blame, three-way diff3).

**Still forward (the faces and the proof tail, not the core):**

- The live conflict-view UI in the surfaces (the moldable-inspector `ConflictView`
  presentation + resolution gadget over the built `resolutions` model).
- The servo content seam: a rendered document / conflict-view as real cap-gated servo
  content, not a text model (§4.3).
- The full cross-party stitch with holes (the partial-turn-promises consent points) and the
  `Regime`↔live-`ConfluenceClassifier` per-region wiring.
- The categorical-pushout Lean residual (§4.4 RESEARCH): the join is proven; the full
  category-`P` construction is named, not built.

### 4.3 The native-substance overhaul (gpui-native · dregg-native · servo-native)

A standing directive frames *how* §4.1–4.2 land: **the old/prototypy web faces get
overhauled to be gpui-native, dregg-native, and servo-native — not bolted onto.** The
existing hypermedia surfaces are deliberately prototypy in named places, and the document
language should drive them *through* their named seams rather than inheriting the
stand-ins:

- **Servo-native (the content, not just the surface).** Today the web-of-cells browser
  renders cap-gated affordance *surfaces* natively, but real `dregg://` *content* is the
  `MockSurface` / `servo_layer_note` stand-in (`web_cells.rs`, `delegate.rs`; the
  `feature = "servo"` `render_dregg_page` path is the first real tile). A document is the
  canonical thing that *needs* real content rendering — so the document language is the
  forcing function to **close the libservo `WebViewDelegate` seam**: a rendered document is a
  servo render-pass over the document cell, cap-gated by the same `SurfaceCapability` the
  membrane projects (the render gate is *in front of* the rasterizer; an out-of-cap region is
  refused in-band). The conflict-view and the transcluded spans render as real content, not
  text models.
- **gpui-native (the cockpit editor).** The native `document` module follows the established
  gpui-free-MODEL + thin-gpui-render discipline (`web_cells.rs`, `INSPECTOR-FRAMEWORK.md`
  §1.3): the patch graph, conflict regions, and presentations are pure data (`cargo test`-able
  without a GPU); the cockpit's gpui layer renders the presentation kinds and arms the
  edit/resolve gadgets generically (the `Halo`/direct-manipulation layer over a document
  `Presentable`). The overhaul is to *promote* the prototypy `DreggverseDocumentView` text
  model into a real moldable gpui editor, not to keep it a panel readout.
- **dregg-native (every edit a verified turn).** The seam that the prototypes only *named*
  is closed by routing every edit/resolution through the real embedded executor — a patch IS
  a turn (`fire_through_world` / `deos-leptos`'s closed-seam `fire_affordance` over a real
  `TurnExecutor`). No parallel document store, no mock dispatch: the document's content is the
  ledger's patch-fold, its commitment is the cell's commitment, its provenance is receipts.
- **The discipline (per the memories): overhaul = drive the seam, never re-haze it.** A
  labeled seam is a *severe problem to close*, not a wall to live behind
  (`feedback-seams-are-work-not-walls`). The document language is precisely the workload that
  makes the servo seam and the prototypy text-models worth closing — so the overhaul is
  *staged-additive-then-cutover* (build the real native face beside the prototype, prove it,
  then cut the prototype over), never a stash-and-rewrite.

This is a cross-cutting *now/soon* thread, not a separate milestone: each piece of §4.1–4.2
lands in its native substance (servo content / gpui editor / executor-backed turn) rather
than as a prototype to be redone later.

### 4.4 An honest now / soon / research split

- **LANDED (the patch core + its first faces).**
  - The `dregg-doc` crate: `DocGraph`, the `Patch` grammar, `apply`/`compose`/`invert`,
    `merge`/`merge_all` (the union/LUB), `resolve_*`, `History` (replay/replay_to/branch/
    stitch), `content` (conflicts as `ConflictRegion`s), `resolutions` (the one-click menu),
    `Doc`/`Granularity` (LCS-diff authoring), `depend`/`blame`/`threeway`/`composition`/
    `literate`. A pure, dependency-free, `cargo test`-able core.
  - A document's *content* is the patch-history fold (`History::replay`/`replay_to`).
  - The substrate ride (behind `--features substrate`): `to_heap_map` + `substrate_commit`
    (the real sorted-Poseidon2 heap root), `executor_drive::ExecutorDrivenDoc` (edits as real
    `TurnExecutor` turns leaving receipts), `desktop::DesktopSurface`; and the `rope` bridge.
  - The cockpit's document editor runs on a live `dregg_doc::Doc`
    (`starbridge-v2/src/deos_desktop/mod.rs`); the deos-zed editor and deos-js composer
    consume `dregg-doc` too (§4.1).

- **SOON (the conflict semantics + the native cutover, end to end).**
  - **Close the servo content seam** for documents: a rendered document / conflict-view as a
    real cap-gated servo render-pass over the document cell, cutting over the `MockSurface` /
    text-model stand-ins (`web_cells.rs` `servo_layer_note`, `delegate.rs` `WebViewDelegate`).
  - The `ConflictView` presentation + the resolution gadget in the moldable inspector, over
    the built `resolutions` model; cross-party resolution as a partial-turn-with-holes (the
    `partial-turn-promises` thread, the linear-logic-forced explicit drop on a contested
    stitch).
  - The `Regime` classifier wired to the live `ConfluenceClassifier` as the per-region regime
    gate (real-conflict vs illusory).
  - Lift the existing `{view,comment,edit,admin}` affordances to per-region edit caps over a
    document cell-subgraph (the membrane and the gate are already there).
  - Rhizomatic's `resolve`/query operators as the monotone document's read/merge face.

- **RESEARCH (the load-bearing proofs and the open questions).**
  - **The merge-correctness proof** for the document patch algebra — that the `dregg-doc`
    `merge` is the **least-upper-bound (the join)** in the document inclusion order `⊑`,
    composing `LaceMerge.lean`'s join with the conflict-antichain representation. This is the
    least-upper-bound join that the pushout *computes* in the Pijul model — the
    `BRANCH-AND-STITCH-PROTOCOL.md` "stitch = pushout" criterion made an executable theorem for
    documents. **LANDED** — `metatheory/Dregg2/Deos/DocMerge.lean` proves it: `DocGraph` is the
    Pijul graph (a **keyed atom map** `AtomId → Option AtomVal` + order-edges + a single-valued
    field store), and `merge` applies the **Dead-wins `Status.join` pointwise** over the atom map
    (`merge_status_dead_wins` is the proof — this is the real status join, *not* a struct-union of
    `Finset`s; the earlier draft modelled the wrong operation). The lattice laws read off the join
    — `merge_comm`, `merge_assoc` (bracket-independent), `merge_idem`, `merge_total`
    (always-defined, the catch the graph model fixes) — and the **universal property**
    `merge_least` + `merge_is_lub` (`merge a b` is the *least* graph including both legs — the
    genuine join; `merge_includes_left`/`merge_includes_right` are the cocone legs). Conflict-as-state
    is a theorem too: `ConflictAt` is an antichain of ≥2 live atoms reachable at one position,
    where the conflict relation uses **transitive reachability** (`Reaches`, the reflexive-transitive
    closure — matching `content.rs::reachable`, not a one-hop shadow); `merge_has_conflict` exhibits
    a concrete two-fork conflict that is a *well-formed* `DocGraph` (not a failure), and
    `resolve_collapses` shows an additive `Connect` patch strictly removes the antichain. The
    two-regime split (§2.4) is connected to `Confluence.IConfluent`: `prose_iconfluent` (grow-only
    content always glues) vs `field_not_iconfluent` (a single-valued field clashes — a constructed
    clashing pair). `#assert_axioms`-clean, `#guard` non-vacuity teeth; `lake build
    Dregg2.Deos.DocMerge` is green. What is **not** built: the file does not construct the
    categorical structure (the category `P`, the span `a ← a⊓b → b`, the functoriality) — so it does
    not prove "THE categorical pushout up to unique iso." It proves the least-upper-bound join that
    the pushout computes in the Pijul model; the full categorical-pushout construction is the named
    residual.
  - **Conflict-as-state soundness** — that a stored conflict state binds, in the document
    cell's commitment, *both* live alternatives + their provenance, so a light client cannot
    be shown a conflict that hides a forged alternative (the `holeFill_binds_in_circuit`
    discipline applied to the conflict antichain).
  - **The granularity question** (genuinely open, *not* asserting a settled answer): what is
    the atom? Character, line, span, or semantic node? Pijul uses byte intervals; the
    `rhizomatic` memory notes dregg's atom *fissioned* (no single delta-atom — the receipt is
    the closest structural homolog). The document atom is a *design choice to make
    empirically*, not a theorem — start span-coarse, refine if it hurts.
  - **The flow-algebra right-skew** (`flow-algebra-right-skew` memory): choice does not
    left-distribute over compose, which is the algebraic fingerprint of "resolve a conflict
    *after* you see what each branch did" — the document editing flow is right-skewed, and
    `FlowRefine.lean::decideRefines` is the decision procedure for "does this resolution
    policy refine that one." Naming the joint; not load-bearing to build first.

---

## 5. THE CONNECTIONS

- **To branch-and-stitch (stitch = pushout).** Publishing a draft is a `Stitch`, which is the
  pushout of §2.1; a contested region is a first-class conflict state instead of a rejected
  merge; the linear-logic-forced explicit drop is the universal-property quotient. The
  document language is *what branch-and-stitch is for* at paragraph granularity — the same
  protocol, the same correctness criterion, finer grain. (`BRANCH-AND-STITCH-PROTOCOL.md`.)

- **To the time-travel semantics (same object).** A document's patch-history is a path through
  the configuration lattice of `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`; an edit is a
  causal-consistent forward move; a draft branch is a divergent configuration; the
  draft-vs-published liveness is the `Rehydration` type. The document inherits
  light-client-unfoolability *for free* (the same replay tooth). Patch theory and the
  event-structure construction are the same object in two notations (the §0 calibration), so
  the document layer and the distributed-branching layer are *one* substrate, not two.

- **To the moldable inspector.** A document is a `Presentable` with multiple presentations:
  `Source` (the EDL / patch source), `DomainVisual` (the rendered document; the `ConflictView`),
  `Provenance` (the patch-history scrubber + the transclusion provenance + the backlinks),
  `Graph` (the `DocGraph` itself, atoms and order-edges). Editing and resolving are `Gadget`s
  on the predict-then-commit spine. The document language is a *consumer* of the inspector
  framework, not a parallel UI. (`INSPECTOR-FRAMEWORK.md`.)

- **To the AOL-wonder front door.** A reader clicks into a document, follows a transcluded
  quote to its source, sees "what links here," scrubs the patch-history — *clicking around,
  absorbing, no comprehension required* (the `AOL-WONDER.md` / deos-ux-vision bar), while an
  adept can open the same document's `Graph`/`Source`/patch presentations and edit it live
  (the Pharo-liveness bar). The conflict-view is *itself* wonder-shaped: "two people wrote
  this differently — here's both, pick one" is legible to a child and exact to an adept.

- **"Let the document language breathe" (what we commit to now vs. let emerge).** ember parked
  the document language to *let it breathe*. So this doc **commits** only to the load-bearing
  shape: a document is a patch-theoretic object on the cell substrate; conflicts are
  first-class states; merge is the pushout; transclusion/backlinks/membrane are the built
  Nelson/Engelbart pieces. It **does not** prematurely freeze: the atom granularity, the exact
  patch surface syntax, the conflict-view UX, the rhizomatic-operator binding, and whether
  documents get their own VC-style "channels" are all left to *emerge* from building the
  small core and using it. The discipline (per the memories): commit the math and the welds
  now; let the language's *surface* and *ergonomics* be discovered by authoring real
  documents on it — not designed in the abstract.

---

## 6. HONESTY LEDGER

**Solid from dregg code read for this doc (read-only, at HEAD):** `DreggverseDocument` /
`Span` / `SpanRange` / `resolve_for` / `RenderedSpan{Own,Transcluded,Darkened}`
(`deos-web-cells/src/document.rs`); `TranscludedField::include`/`verify`/`project_for`,
`Provenance`, `Backlinks`/`Observer` (`starbridge-web-surface/src/transclusion.rs`);
`Membrane::project`/`reshare`, `meet_rights` = `is_attenuation`, `Rehydration::classify`,
`Sturdyref`/`rehydrate` (`starbridge-web-surface/src/rehydrate.rs`); the web-of-cells browser
+ the per-viewer document weld + the `{view,comment,edit,admin}` affordance surface + the
powerbox-upgraded `SemiReinteractiveTransclusion` (`starbridge-v2/src/web_cells.rs`); the
two-way `DreggverseMap`/`LinksHerePanel` per-viewer fog (`dreggverse_map.rs`, `links_here.rs`);
`deos-leptos` cell-state = `RwSignal`, affordance-fire = real executor turn, the closed seam
(`deos-leptos/src/lib.rs`); the Presentable/Gadget framework + the predict-then-commit spine
(`INSPECTOR-FRAMEWORK.md`); the patch-theory ≅ event-structure calibration, `LaceMerge`/
`Confluence`/`ConfluenceClassifier`, the I-confluent fragment, the stitch = pushout
(`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`, `BRANCH-AND-STITCH-PROTOCOL.md`, the
`rhizomatic-dregg-slotting` + `distributed-houyhnhnm-frontier` memories); and the
**`dregg-doc` crate** — the Pijul-shaped patch core IS built (`dregg-doc/src/{graph,atom,
patch,merge,history,content,regime,resolve,resolution,doc,depend,blame,threeway,composition,
literate,commit}.rs`, plus the substrate-gated `substrate`/`executor_drive`/`desktop` and the
`rope` bridge), `cargo test`-able as its own dependency-free workspace, and already consumed
by the deos desktop editor, deos-zed, and deos-js. Confirmed: `DreggverseDocument`
(`deos-web-cells/src/document.rs`) is still **content-flat** (an ordered `Vec<Span>` EDL, no
patch history of its own) — `dregg-doc` is the patch layer that produces such a rendering.

**Prior art — cited from memory; confirm dates/attributions before this goes outward:**
Ted Nelson, *Literary Machines* (~1981), Project Xanadu / transclusion (1965–); Douglas
Engelbart, NLS / the 1968 "Mother of All Demos"; David Roundy et al., **Darcs** (the
"theory of patches," ~2005); Samuel Mimram & Cinzia Di Giusto, *A Categorical Theory of
Patches* (MSCS / arXiv, ~2013) — merge = pushout, conflicts as first-class objects;
Pierre-Étienne Meunier et al., **Pijul** (~2017–; the graph-of-alive/dead-vertices model,
patches as graph operations, the pseudo-graph that makes merges total). The
concurrency-theory side (Winskel event structures, Danos–Krivine RCCS, Goguen sheaf
semantics, Mattern consistent cuts) is cited in full in
`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §7. I am confident in the *substance* (what each
result says and why it applies — especially the merge-as-pushout and conflicts-as-states
core); the years/venues are the spot-check.

---

*( ˘▾˘ ) a closing couplet, since a document turned out to be a graph we may grow:*

*two pens that crossed a paragraph need not be told to choose —*
*the conflict is a state to hold, a patch away from news.*
