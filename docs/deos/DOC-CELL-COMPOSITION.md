# THE DOCUMENT COMPOSITION ALGEBRA
## A document *composed from* cells — embed whole child cells, each independently owned/capped/versioned, into one rendered whole

*A design exploration (think-with, not a spec). The companion docs are
`DOCUMENT-LANGUAGE.md` (the patch core a single document cell already is),
`BRANCH-AND-STITCH-PROTOCOL.md` (stitch = pushout), `INSPECTOR-FRAMEWORK.md`
(the Presentable substrate), and the Lean `Dregg2/Deos/Transclusion.lean` (the
verified field-value quote). It is honest about what is built, what is a bounded
prototype, and what is speculative.*

---

## 0. THE ONE-SENTENCE QUESTION, AND ITS ONE-SENTENCE ANSWER

> **Today a dreggverse document IS a cell (1:1) — one `DocGraph` whose atoms fold
> to content. Should a document instead be *composed from* cells — a tree/graph
> of cells, a section IS a cell, a figure IS a cell, each independently owned,
> capped, and versioned, laid out into one rendered whole?**

**Answer: yes, and the move is one new atom kind, not a new substrate.** Today an
atom carries a `String`. A *composed* document adds one more thing an atom can
be: a **cell-pointer** (`Op::Embed { child, … }`). The parent document stays a
`DocGraph` and keeps every property it already has (patch-fold content, total
union-merge, first-class conflicts, provenance-binding commitment); the embed-atom
is a *hole in the parent's content* that the renderer fills by **resolving the
child cell through the viewer's membrane**. The composition operator is
"`Embed` an atom that points at a `dregg://` child"; ownership is "the child is
its own cell with its own caps"; cross-cell merge is "the parent's layout graph
and each child's graph merge *independently* — they never share a graph, so a
child edit can never conflict with a layout edit"; and what `dregg-doc` gains is
exactly one `Op` variant + a render-time resolver. **The whole starbridge is
kinda like a cell document** because this is what the desktop already is — a
surface composed from cell-surfaces; the document language is that same
composition, named and given a patch algebra.

---

## 1. THE DISTINCTION THAT MAKES THIS CLEAN: *transclude a value* vs *embed a cell*

The single most load-bearing idea in this doc is that **composition is NOT
transclusion**, and conflating them is the trap. dregg already has transclusion,
fully and verifiedly:

- **Transclusion** (`Dregg2/Deos/Transclusion.lean`, `starbridge-web-surface/src/transclusion.rs`,
  the Lean `ImportedEq`) imports a **field VALUE**: "my local field holds the
  *bytes the source cell committed* at a cited, immutable receipt." It is a
  *quote*. The four proven Xanadu properties — `transclusion_is_observed_finalized_read`,
  `transclusion_provenance_faithful`, `transclusion_no_amplify`,
  `transclusion_stable_under_source_advance` — are all about a *value*: the quote
  equals the committed value, a forge can't be cited, the quote is a read not a
  key, and the citation pins an immutable past so the quote **never rots** (it is
  a snapshot of a *finalized* receipt; the source advancing leaves it unchanged).

- **Composition** embeds a whole **CELL**: "this section *is* the cell
  `dregg://<child>`, owned by someone else, **rendered live** (or at a pinned
  version), laid out inside my document." It is not a value-quote — it is a
  *subtree*. The child has its own atoms, its own caps, its own patch history,
  its own commitment. The parent does not copy the child's bytes into a field;
  the parent *points* at the child and the renderer *recurses*.

The two compose (a composed child may itself transclude a value), but they are
different operators with different semantics on every axis:

| axis | **transclude (value)** | **embed (cell)** — NEW |
|---|---|---|
| what is included | a field value (bytes the source committed) | a whole child cell (atoms + edges + fields) |
| liveness | a **snapshot** of a finalized receipt (never rots, never updates) | **live** by default (re-resolves to the child's tip) OR pinned to a child receipt |
| ownership | the value's source cell | the child cell — *independently owned/capped/versioned* |
| edit | you cannot edit a quote (it is the source's committed value) | you can edit the child *if you hold its `edit` cap* — a turn on the child |
| merge | n/a (a value, not a graph) | the child's graph merges *independently* of the parent layout |
| failure-to-resolve | the quote is the cited past, always available | the child may be unreachable → renders **darkened** (the membrane projection) |

So: **transclusion is the Xanadu quote (built, proven); composition is the new
operator this doc designs.** Keeping them distinct is what keeps the algebra
sound — an embed is a *reference into the web-of-cells*, not a value baked into
the parent's commitment.

---

## 2. THE COMPOSITION OPERATOR — `Op::Embed`, an atom that is a cell-pointer

### 2.1 The shape

Today (`dregg-doc/src/patch.rs`) the patch grammar is `Add` / `Delete` /
`Connect` / `SetField`. The `Add` op introduces an atom carrying `String`
content. Composition adds **one op**:

```rust
Op::Embed {
    id: AtomId,        // the embed-atom's own content-addressed id (a layout vertex)
    child: ChildRef,   // WHICH cell, and at what version
    after: AtomId,     // where it sits in the parent's order (same anchoring as Add)
    role: EmbedRole,   // how it lays out (Section / Figure / Inline / Block / Citation)
}
```

where the new payload types are:

```rust
enum ChildRef {
    Cell(CellId, Pin),         // this exact cell (stable IDENTITY) — content-addressed, unforgeable
    Name(DreggUri, Pin),       // whatever a NAMESPACE currently binds this name to (re-bindable)
}
struct DreggUri { namespace: CellId, name: String }   // a name in a namespace cell's binding map
enum Pin { Live, At(ReceiptHash) }   // Live = render the tip; At = a pinned receipt (an embed that never rots)
enum EmbedRole { Section, Figure, Inline, Block, Citation }
```

`ChildRef` has **two arms** — this is the binding-vs-identity distinction, the
single load-bearing refinement of the operator (see §2.1b). Both arms carry a
`Pin`, so either can render live or freeze to a receipt.

An embed-atom is a *layout vertex* in the parent's `DocGraph`: it has an id, a
status (alive/dead — you can tombstone an embed to remove a section, monotone, no
loss), provenance (who placed it), and an order-edge (`after -> id`) exactly like
a content atom. **The only difference from a content atom is what it renders to:**
a content atom renders its `String`; an embed-atom renders the *resolved child
cell* in its place.

The cleanest implementation keeps `Atom` uniform by making content a sum:

```rust
enum AtomContent {
    Text(String),     // today's atom — a content span
    Embed(ChildRef, EmbedRole),   // NEW — a cell-pointer the renderer recurses into
}
```

This is the **least-invasive shape**: `Atom` gains a richer `content`, every
existing primitive (insert / tombstone / connect / merge / commit) works
unchanged on embed-atoms because they treat content opaquely, and the *only* new
code is (a) the `Embed` op desugars to "insert this atom + connect," and (b) the
renderer recurses on an `Embed` atom instead of emitting a string. The prototype
(`composition.rs`) takes exactly this shape, kept self-contained so it does not
perturb the existing `Atom`.

### 2.1b BINDING vs IDENTITY — the two arms of `ChildRef` (the load-bearing refinement)

A raw `CellId` is the right handle for **IDENTITY** — it is stable,
content-addressed, the address *is* the cell; the cell's *state* evolves under
that one id forever, and (for a recoverable identity cell) its authorized keys
**rotate in-state** while the id is unchanged (§3.5). But at the
application/semantic level you very often do not want a fixed address — you want
*"whatever cell plays this ROLE right now."* "The hero figure." "The current
governing clause." "The active theme." That is a **re-bindable reference**: a
name in a namespace, whose binding a turn can move, with the embed following.

So `ChildRef` has two arms, differing on exactly one axis — *fixed identity* vs
*re-bindable binding*:

| | `Cell(CellId, Pin)` — IDENTITY | `Name(DreggUri, Pin)` — BINDING |
|---|---|---|
| what it points at | this exact cell, by its content-addressed id | whatever the namespace binds the name to *right now* |
| resolution | direct: the id IS the handle | a name step first (`namespace.resolve_name` → `CellId`), then resolve the cell as `Cell` does |
| what a turn moves | the cell's *state* (the id is immutable) | the *binding* (a `SetField` on the namespace cell; the cell's own id is untouched) |
| does it follow a rebind? | **no** — pinned to the identity (§3a) | **yes** — the embed re-resolves the name every render (§3a) |
| does it survive the child's key rotation? | **yes** — the id is inception-anchored, stable across recovery (§3.5, §3b) | yes, transitively (the *binding's current cell* survives its own rotation) |
| unbound state | n/a (an id always denotes a cell) | a `Name` may bind to nothing → `ChildResolution::Unbound` (a first-class state; a later bind heals it) |
| commitment binds (§3.3) | `id ‖ pin ‖ role ‖ provenance` | `namespace ‖ name ‖ pin ‖ role ‖ provenance` — the *indirection itself* is committed; a light client follows the same name |
| the right tool for | "this specific figure, by that illustrator" | "the figure that plays the hero role here" |

The namespace is **not a new substrate** — it reuses the existing nameservice
binding: a namespace cell holds a single-valued `name -> CellId` field
(`cli/src/commands/name.rs`'s `RESOLVE_TARGET_SLOT` `SetField`, or the
governed-namespace route-table), and a rebind is a turn that rewrites it. The
prototype's `NamespaceResolver` (with the in-memory `MapNamespace`) is the
standalone analogue; the `substrate` resolver consults `WebOfCells` (cells + the
nameservice binding). The resolver does the name step **every render**, which is
exactly why a `Name` embed follows a rebind for free — the document never
changes, only the namespace does.

The two arms are the same operator at two granularities of *what stays fixed*:
`Cell` fixes the identity and lets the state move; `Name` fixes the *role* and
lets the identity move. A `Name` embed can still be pinned (`Name(uri, At(r))`):
the name resolves to today's cell, but the rendered *version* is frozen — so even
a re-bindable reference can cite an immutable past.

### 2.2 Why a pointer, not a copy (and why this is the *right* substrate fit)

A composed document is a **graph of cells** — the parent's layout `DocGraph`
plus, by reference, each child's `DocGraph`. The parent never holds the child's
bytes; it holds the child's `CellId` (content-addressed, unforgeable: the address
*is* the identity) and a `Pin`. This is the web-of-cells `dregg://` addressing
(`web_of_cells.rs::DreggUri`) used *inside* a document. Three consequences fall
out for free, each from a property the substrate already proves:

1. **The embed is unforgeable.** A `CellId` is `blake3` of the cell's genesis;
   you cannot point at a cell that does not exist, and two embeds of "the same
   child" are the same `CellId` (idempotence — the same composition authored
   twice is one embed).
2. **The embed confers no authority over the child.** Resolving an embed is a
   *read through the membrane* — `transclusion_no_amplify`'s sibling: embedding a
   peer's cell does not hand you the peer's cell. You render what your caps let
   you read; an out-of-cap child renders **darkened** (provenance survives, bytes
   withheld — exactly `DreggverseDocument::resolve_for`'s darkened span).
3. **A `Live` embed tracks the child; a pinned embed never rots.** `Pin::Live`
   re-resolves to the child's tip every render — the section updates when its
   owner edits it (the desktop-liveness bar). `Pin::At(receipt)` pins an
   immutable child receipt — the *composition* analogue of
   `transclusion_stable_under_source_advance`: a pinned embed is a citation that
   does not break, ever, no matter what the child does next.

### 2.3 The render = the recursive fold

Rendering a composed document is the existing `content()` walk
(`dregg-doc/src/content.rs`) with one new case: when the walk reaches an
embed-atom, instead of pushing `Segment::Clean(text)` it pushes a
`Segment::Embedded(resolved)` where `resolved` is the **child cell rendered
through the viewer's membrane** — itself a `Rendered` (so the fold is genuinely
recursive; a child may compose grandchildren). The render is parameterized by a
**resolver** (`fn(&ChildRef, &Viewer) -> ChildResolution`) so the core stays
substrate-free: the standalone crate ships a trait, the `substrate` feature
plugs in the real `dregg://` fetch + membrane projection.

```
content(parent, viewer, resolver):
  walk the parent DocGraph as today, but at an embed-atom E:
    child = resolver.resolve(E.child, viewer)     // membrane-gated; may be Darkened
    emit Segment::Embedded { role: E.role, provenance: E.provenance, child }
```

A `ChildResolution` is one of: `Rendered(Box<Rendered>)` (you could read it — the
recursion), `Darkened { cell, reason }` (your caps don't reach it — the membrane
withheld it, citation kept), or `Unresolved { cell }` (the child cell could not
be fetched at all — a real failure, surfaced not swallowed). **The renderer never
forges and never panics** — an unreachable or out-of-cap child is a first-class
*state* of the rendered output, the same discipline conflicts get.

---

## 3. OWNERSHIP / AUTHORITY — composing a doc from cells you don't own

This is where composition earns its keep, and where the substrate already does
the work.

### 3.1 Each child contributes under *its own* caps

A composed document is the canonical case of "you compose from cells you don't
own." A figure cell is owned by the illustrator; a data-table cell by the
analyst; a quoted clause cell by a third party. The parent document's author
holds:

- the **`edit` cap on the parent layout cell** — to place / remove / reorder
  embeds (a layout edit is a turn on the *parent* cell), and
- whatever **caps the child cells' owners granted them** — `view` (render it),
  maybe `comment`, maybe `edit` (edit the child *in place*).

The crucial fact: **the parent's layout authority and each child's content
authority are SEPARATE caps on SEPARATE cells.** Placing an embed needs only the
parent's `edit` cap (you may compose a doc from a child you can merely *view* —
you place a pointer, you don't touch the child). Editing the embedded child needs
the *child's* `edit` cap, conferred by the child's owner through the powerbox —
exactly the `SemiReinteractiveTransclusion` upgrade shape (`web_cells.rs`): a
read-only embed becomes an editable one *only* through a real, attenuated grant.

So the `{view, comment, edit, admin}` affordance set (`web_cells.rs`) applies
*per cell*, and a composed document is a **frustum of caps**: each region renders
under the meet of the viewer's caps and the child owner's grant. An out-of-cap
child is darkened (read withheld); an in-view-but-not-edit child renders but its
edit gadget is absent; an in-edit child is live-editable. This is the membrane
(`Membrane::project`, `meet_rights = is_attenuation`) lifted from "regions of one
cell" to "the cells a document is composed from."

### 3.2 The authority NEVER amplifies through composition

The standing law (`transclusion_no_amplify`, `Membrane::reshareN_attenuates`):
composing a child confers no authority over it beyond what you were granted. If
you can only `view` a child, embedding it in your document and re-sharing your
document does not let your readers `edit` the child — your document's grant is the
*meet* of (what you hold on the child) and (what you grant on your document). The
Lean keystone `transclusion_grants_no_unheld_authority` is the exact tooth: an
authority you never held over the child cannot be conjured by naming it in a
composed-document request. **A document composed from cells you don't own is
safe by the same non-amplification proof the membrane already carries** — this is
a *naming*, not new mathematics, and the prototype's resolver enforces it
structurally (the resolver is handed the viewer's caps and can only ever return
an attenuated view).

### 3.3 The embed's commitment binds the *pointer*, not the child's bytes

A subtle, load-bearing soundness point. The parent's commitment
(`dregg-doc/src/composition.rs`) must bind the embed-atom — but it
binds the **`ChildRef` (cell id + pin) + role + provenance**, *not* the child's
content. The child's content is committed in the *child's own* `heap_root`. This
is correct and necessary:

- A `Pin::At(receipt)` embed binds an immutable child receipt; a light client
  verifies the child separately (fetch the child, check its root equals the
  pinned receipt's commitment) — the composition is *verifiably what was placed*,
  the child is *verifiably what it committed*, and the two checks compose. You
  cannot be shown a pinned embed that secretly points elsewhere (the `ChildRef`
  is in the parent's commitment) nor a child whose bytes were forged (the child's
  own root catches it).
- A `Pin::Live` embed binds the *cell id* (which child) but explicitly NOT a
  version — the parent commits "this section is the live child cell `C`," and the
  rendered bytes are whatever `C` committed at render time, verified against `C`'s
  current root. The parent's commitment is *honest about the indirection*: it
  commits a pointer, and the renderer (and a light client) follows it.

The prototype extends the existing leaf scheme (`substrate.rs::to_heap_map`) with
an embed leaf: `COLL_EMBEDS` binding `id ‖ cell ‖ pin ‖ role ‖ provenance`. The
anti-forge tooth survives unchanged — forging which child an embed points at, or
its pin, changes the embed leaf, changes the parent root.

---

### 3.4 The concrete resolver: a whole-cell transclusion as a per-viewer attenuated VIEW

§2.3's render-fold is parameterized by a `resolver` (`fn(&ChildRef, &Viewer) ->
ChildResolution`) so the patch core stays substrate-free. This section pins the
*concrete substrate-backed resolver* the `substrate` feature plugs in — the
realization §8 names as a residual — and states it as its own first-class object,
because it is the precise sense in which an embed is **a living, capability-confined
inclusion of one cell inside another's document**, not a copy: a *whole-cell
transclusion*.

The field-value quote and the whole-cell embed are the same construction at two
granularities, and the lift is *one design move — cite a surface, not a scalar*:

| | field-value transclusion | **whole-cell transclusion** |
|---|---|---|
| what is cited | one finalized field VALUE | the source cell's finalized **surface root** |
| the kernel handle | a scalar in a `Provenance` | `Target::Surface(cell)` — a `Cap.endpoint cell rights` (`Dregg2/Deos/Surface.lean`: `surfaceConfersExactly` — a window confers EXACTLY its rights, the pixels add zero authority) |
| what a reader sees | the quoted bytes (or darkened) | a **per-viewer attenuated VIEW of the whole cell**: its affordance set projected to the reader's caps, its sub-document, its rehydratable surface (or darkened) |
| anti-forge | `TranscludedField::verify` on the value | the *same* `verify` on the surface root — a forged surface cannot be cited |
| non-amplification | `transclusion_no_amplify` (the value) | the *same* `Membrane::reshareN_attenuates` (the whole-cell view) |
| no-rot | `transclusion_stable_under_source_advance` | the *same* — the cited surface root pins an immutable receipt |

The crucial property — **fog-of-war inside a document** — is that the embed is
resolved *per reader through their own caps*. The resolver is exactly the membrane
meet, lifted from "regions of one cell" (§3.1) to "an embedded cell": for reader `V`,

```
project_for(V) =
  let cap   = V.held  ⋀_membrane  embed.lineage            -- Membrane::project (real is_attenuation lattice)
  in  case cap of
        Ok(c)  -> Visible { rights: c.rights,
                            affordances: source_surface.project_for(c) }   -- AffordanceSurface::project_for
        Refuse -> Darkened                                  -- incomparable authority: no view both admit; provenance KEPT
```

Three teeth fall out, all on the existing proofs:

1. **Each reader sees the embed at *their own* cap level.** A `view`-tier reader sees
   only the embedded cell's `view` affordance; an `edit`-tier reader sees
   `view`+`comment`+`edit`; an `admin` sees all — the *same embed*, projected to
   different frusta. The weaker view is a strict subset of the stronger (the embedded
   cell is itself a per-viewer frustum). This is `AffordanceSurface::project_for`
   (`web_cells.rs`) run on the *meet* cap, so it is the same progressive-attenuation
   the desktop already does, now scoped to an embed.
2. **An over-reach darkens, never forges.** A reader whose authority is *incomparable*
   with the embed's lineage (e.g. holding `Proof` against an `Either` lineage — neither
   attenuates the other) gets **no view both admit**: the embed darkens. Its provenance
   *survives* (the reader always knows *which* cell is embedded and that it is genuinely
   cited) but its surface and affordances are withheld — the whole-cell analogue of
   `DocumentSpanKind::Darkened`. The renderer never substitutes, never fabricates.
3. **The embed cannot amplify across a reshare hop.** When a holder re-shares the embed
   downstream, the downstream cap must attenuate what the holder held (`Membrane::reshare`
   = the real `is_attenuation` per axis: window rights, fetch/navigate allowlists,
   permissions). A hop that tries to grant the downstream reader *more* authority over
   the embedded cell — widening rights, or re-adding a dropped origin — is **refused**
   (`RehydrateError::Amplification`). This is `reshareN_attenuates` /
   `reshare_refuses_amplification` verbatim, so however many hops an embed travels, the
   last holder's authority over the embedded cell is bounded by the first holder's.

And it composes with the affordance/rehydration stack at no extra cost: an embedded
cell rehydrates per-viewer through `web_aff::rehydrate`, carrying the derived
`Rehydration` liveness-type (LIVE / REPLAYED-DETERMINISTIC / RECONSTRUCTED-APPROXIMATE)
— so an embed is not a dead snapshot but a liveness-typed re-expansion of a witnessed
cell, exactly the object a rehydrated surface is (this is the realization of §7's
"live-embed liveness-typing" residual at the resolution boundary).

**Prototype (this work):** `starbridge-v2/src/cell_transclusion.rs` — the concrete
substrate-backed resolver §8 named, gpui-free and `cargo test`-able beside `web_cells.rs`:
`WholeCellTransclusion::{embed, project_for, reshare_to, rehydrate_embed}` over the REAL
`TranscludedField` (provenance/forge/no-rot) + `Membrane` (per-viewer meet, reshare
non-amp) + `AffordanceSurface::project_for` (the per-viewer affordance set);
`EmbeddedCellView::{Visible{viewer_cap_rights, affordances}, Darkened}` is the concrete
`ChildResolution`; `ComposedCellDocument`/`resolve_for` resolves a *whole document
composed from cells* per-viewer (host's own affordances + each embed, one membrane).
Both polarities bite: a viewer sees the embed at their cap level
(`each_reader_sees_the_embed_at_their_own_cap_level` — `view` ⊂ `view,comment,edit`),
an over-reach darkens (`an_overreach_reader_sees_the_embed_darkened`), a resharing
amplification is refused (`resharing_the_embed_cannot_amplify`), and a document with a
mix darkens only the out-of-reach embed while the rest stays usable
(`a_reader_darkens_one_embed_but_sees_the_rest`). The prototype is the runtime
*resolution* sibling of the patch-core `composition.rs` *structural* operator — theirs
binds the embed pointer into the layout graph + commitment; this projects that pointer
into a per-viewer view through the live cap stack. They meet at §2.3's resolver seam.

---

### 3.5 THE IDENTITY-CELL-ID-STABILITY FINDING (the load-bearing fact under the `Cell` arm)

The `Cell` arm's whole value — "embed this exact identity, and it stays embedded
across the child's recovery" — rests on one substrate fact, established by census
(reported here, not assumed): **a recoverable identity cell's `CellId` is stable
across key rotation.** The derivation, verbatim from the code:

```
CellId = blake3_derive_key("dregg-cell-id-v1", genesis_pubkey ‖ token_id)
```
(`types/src/lib.rs::CellId::derive_raw`). Both `genesis_pubkey` and `token_id`
are **SEALED at inception** — `pub(crate)`, never mutated; the invariant
`id == derive_raw(public_key, token_id)` is re-checked on every ledger update
(`cell/src/cell.rs`, `Cell::verify_id_integrity`). Key rotation / recovery is a
**`SetField` on a key-COMMITMENT state slot**, never the sealed pubkey:

```rust
// sdk/src/identity.rs::rotate_effects — KERI pre-rotation:
set(cell, CURRENT_KEYS_COMMIT_SLOT, presented_commit),   // install the new key set's commitment
set(cell, NEXT_KEYS_DIGEST_SLOT,    fresh_next_digest),   // pre-commit the next set
set(cell, LAST_ROTATED_AT_SLOT,     height),
```

and the rotate verb is proven in Lean to be **independent of the current keys**:
`metatheory/Dregg2/Apps/PreRotation.lean::rotate_current_keys_irrelevant` is `rfl`
— admission and post-state read only `nextDigest` and the event, *never* the
cell's identity. The recovery e2e (`sdk/tests/identity_social_recovery_e2e.rs`)
asserts the recovered identity's cell id is unchanged after a full guardian-quorum
key replacement.

**VERDICT: the identity-cell id is STABLE across key rotation — inception-anchored,
not current-key-bound.** Therefore a `Cell(id)` embed of an identity cell is
**unbroken across that cell's recovery**: the embed never needs re-authoring when
the child rotates its keys. *(The counterfactual is the loud finding that would
matter if it were true: were the id current-key-bound, rotation would mint a new
id and every `Cell(id)` embed of it would dangle. It is not — the embed-survives-
rotation proof exhibits exactly that broken world to show the substrate is not
it.)*

This is also *why both arms compose cleanly*: the `Name` arm's "follow the
binding" and the `Cell` arm's "survive rotation" are independent — a `Name` embed
of a name bound to an identity cell follows rebinds (the binding can move) AND its
current binding survives that cell's rotation (the bound cell's id is stable). The
two kinds of mutation (rebind the *name*, rotate the *keys*) live on different
cells and neither breaks the embed.

---

## 4. MERGE / CONFLICT ACROSS COMPOSED CELLS — the pushout that *cannot* cross the boundary

This is the deepest payoff, and it is *better* than the single-cell case because
**composition is a confinement boundary.**

### 4.1 Children and layout merge *independently* — no cross-graph conflict is possible

A composed document is two (or more) **separate `DocGraph`s**: the parent layout
graph and each child's graph. They are merged by **separate pushouts**:

- Two authors who **reorder/add/remove embeds** edit the *parent layout graph*.
  Their edits merge by the existing `merge` (`dregg-doc/src/merge.rs`) — the total
  union pushout. A layout conflict (two authors place two different children at
  the same position with no order between them) is a first-class prose-antichain
  conflict in the *parent* graph, resolved by a `Connect` exactly as today. **The
  embed-atoms are just atoms; the layout algebra is unchanged.**
- Two authors who **edit the same child** edit the *child's* graph. Their edits
  merge by the child's own pushout, producing a conflict *in the child*, resolved
  *in the child*, by whoever holds the child's `edit` cap.

The structural theorem (the one worth proving in Lean): **a child-content edit
and a parent-layout edit can NEVER conflict with each other, because they touch
disjoint graphs.** This is the patch-theory "patches that touch disjoint parts of
the graph commute" (`DOCUMENT-LANGUAGE.md` §2.2) lifted to the *cell* boundary:
the parent's atoms and the child's atoms are in different cells with different
`AtomId` spaces, so their union is unconditionally clean. Composition turns "the
whole document is one conflict surface" into "each cell is its own small conflict
surface, and the layout is a third" — **conflicts are localized to the cell they
belong to.** A contested figure does not conflict with a contested paragraph
three sections away; each resolves independently, by its own owner, while the
rest of the document stays fully usable. This is the §2.3 "don't block the whole
document on one contested paragraph" insight taken to its natural granularity:
*don't block the document on one contested cell.*

### 4.2 The merged whole = the pushout of the *layout* with the children resolved pointwise

Formally, merging two composed documents `D₁ = (L₁, {children})` and
`D₂ = (L₂, {children})`:

```
merge(D₁, D₂) = ( merge(L₁, L₂),                          -- the layout pushout (existing)
                  { c : merge(child₁ c, child₂ c) | c } ) -- each child's pushout, independently
```

This is a **product of pushouts** — the merge factors through the composition
structure. Commutativity, associativity, idempotence, totality all hold
*componentwise* (each is the existing single-graph `merge`'s property), so the
composed merge inherits them. The only genuinely new obligation is the
**boundary lemma**: `merge` on the parent never touches a child's graph and vice
versa (true by construction — disjoint `CellId`s, disjoint `AtomId` spaces). The
prototype demonstrates this with `merge_composed`: two authors reorder embeds
(layout pushout) while a third edits an embedded child (child pushout), and the
three results compose with no cross-conflict.

### 4.3 The one *real* cross-boundary conflict: a `Pin::At` divergence

There is exactly one place composition introduces a *new* conflict kind, and it
is a **`Regime::Field`-style (non-monotone) conflict**: two authors pin the
*same* embed to *different* child receipts (author A pins the figure at v3, author
B at v5). This is a single-valued clash — an embed has one pin — so it surfaces
as a first-class conflict at the non-monotone boundary the `Regime` classifier
already draws, resolved by *choosing a pin* (or going `Live`). It is the
`SetField` clash (`regime.rs::Regime::Field`) specialized to the embed's pin: the
prototype models the pin as exactly this, so a pin-divergence reuses the existing
field-conflict machinery (`append_field_conflicts`, the resolution gadget) with
zero new conflict code. A `Live` embed has no pin and so *cannot* pin-conflict —
liveness sidesteps the only new conflict kind.

---

## 5. WHAT `dregg-doc` GAINS — the exact delta

A precise, bounded list (the prototype builds the standalone half; the substrate
half is the named wiring):

1. **`Op::Embed` + `AtomContent::{Text, Embed}`** — the one new op and the atom
   becoming a sum (text-span OR cell-pointer). Every existing primitive works
   unchanged because it treats content opaquely. *(prototype: `composition.rs`)*
2. **`ChildRef = Cell(CellId, Pin) | Name(DreggUri, Pin)`, `Pin::{Live, At}`,
   `EmbedRole`** — the embed payload, with the **two-arm binding-vs-identity**
   refinement (§2.1b): a `Cell` arm (fixed identity, evolving state, stable across
   key rotation §3.5) and a `Name` arm (re-bindable namespace reference, follows a
   rebind). *(prototype)*
3. **A recursive resolver seam with a name step** — `trait ChildResolver` with
   `resolve_cell(cell, viewer, …)` + a `namespace() -> &dyn NamespaceResolver`,
   and a default `resolve(&ChildRef, …)` that resolves the `Name` arm through the
   namespace FIRST (`Unbound` if it binds nothing), THEN the cell. `trait
   NamespaceResolver { fn resolve_name(&DreggUri) -> Option<CellId> }` (in-memory
   `MapNamespace` / `NoNamespace`). `ChildResolution::{Rendered, Darkened,
   Unresolved, Cycle, Unbound}`. The standalone crate ships the traits + the
   in-memory `MapResolver` (cells + namespace); the `substrate` feature plugs in
   the real `dregg://` fetch + `WebOfCells` nameservice + `Membrane::project`.
   *(prototype: traits + MapResolver/MapNamespace; substrate impl = named wiring)*
4. **`content_composed(parent, viewer, resolver)`** — the recursive fold that
   emits `Segment::Embedded` for embed-atoms. *(prototype)*
5. **`merge_composed`** — the product-of-pushouts merge (layout pushout + each
   child's pushout). *(prototype, in-memory children)*
6. **The pin-divergence conflict** — modeled as the existing field clash on the
   embed's pin. *(prototype)*
7. **`COLL_EMBEDS` leaf** in `substrate.rs::to_heap_map` — binds, per arm, the
   *pointer* (not the child's bytes): for a `Cell` embed `id ‖ cell ‖ pin ‖ role ‖
   provenance`; for a `Name` embed `id ‖ namespace ‖ name ‖ pin ‖ role ‖
   provenance` (the indirection itself committed, so a light client follows the
   same name). *(named wiring — substrate-feature)*
8. **The substrate resolver** — `ChildResolver` backed by `WebOfCells::fetch` +
   `Membrane::project`, plus a `NamespaceResolver` backed by the `WebOfCells`
   nameservice binding (`cli/src/commands/name.rs`'s `RESOLVE_TARGET_SLOT`
   `SetField`, or the governed route-table), so a `Cell` embed is a real cap-gated
   `dregg://` read and a `Name` embed is a real cap-gated read of the namespace's
   *current* binding. *(named wiring — the §4.3-dregg-native seam)*

Items 1–6 are the standalone algebra (prototyped, `cargo test`-able with no
substrate). Items 7–8 are the substrate ride (named, behind the `substrate`
feature, reported for ember to wire — not edited into shared files here).

---

## 6. "THE WHOLE STARBRIDGE IS KINDA LIKE A CELL DOCUMENT"

ember's aside is exactly right and worth making precise, because it is the
*validation* of the model: **the desktop is already a composed-cell document.**
The starbridge cockpit (`starbridge-v2`) is a surface composed from cell-surfaces
— the web-of-cells browser lays out affordance surfaces of many cells, each
cap-gated, each rendered per-viewer through the membrane, each independently
owned. That is *structurally* an `Op::Embed` tree: the desktop is the root layout
cell, each window/panel is an embedded child cell, the moldable inspector is the
recursive renderer, and the Halo/direct-manipulation layer is the edit-gadget on
each embed. The document composition algebra is **the same object the desktop
already is**, given a patch history and a conflict semantics. Two consequences:

- The document editor does not need a new compositor — it is a `Presentable`
  consumer (`INSPECTOR-FRAMEWORK.md`): a composed document's `DomainVisual`
  presentation renders the embed tree the way the desktop renders the surface
  tree, and the `Graph` presentation shows the layout `DocGraph` with embed-atoms
  as cell-pointer nodes. Composition is a *consumer* of the cockpit, not a
  parallel UI.
- The convergence is the design's own correctness check: if "a document composed
  from cells" did *not* land on the same shape as "a desktop composed from cell-
  surfaces," one of them would be wrong. They land on the same shape — an embed
  tree of independently-owned, membrane-projected, cap-gated cells — which is the
  evidence the operator is the natural one.

### 6.1 The reflexive projection, made executable (the desktop-document prototype)

§6's claim is qualitative ("the desktop is *structurally* an embed tree"). This
section makes it a **running fold**: there is a real, green projection of the live
cockpit workspace into a `dregg_doc` document, committed by the REAL substrate heap
root. It does not need `Op::Embed` (§2) — the desktop's structure is *flatter and
more immediate* than a recursive embed tree: it is exactly the shape `dregg_doc`
already has (an ordered graph of atoms + a single-valued field store). That is the
sharper form of the convergence check — not just "the same operator," but **the
same data model, no new op required.**

**The objects it welds (both already real, census-first):**

- the cockpit's **scene graph** — `compositor::CompositorScene` is an *ordered list*
  of `compositor::CompositedSurface`, each `(owner: CellId, regions, content_digest,
  source_state_root, z_layer, focus_flag)`. The z-order IS an order relation; each
  surface IS a window onto a cell. (Read at HEAD: `starbridge-v2/src/compositor.rs`.)
- the workspace's **cell-backed UI state** — `view_cell::WorkspaceCell` (the active-tab
  selector, a real cell whose nonce is the workspace revision) composing child
  `view_cell::ViewCell`s (each a per-view camera-aim cell, *itself* `Presentable` —
  "inspect the inspector"). The UI state is *already* witnessed cells, not Rust
  fields. (Read at HEAD: `starbridge-v2/src/view_cell.rs`.)

**The projection (the mechanical map):**

| desktop notion | document notion |
|---|---|
| a surface (a window onto a cell) | an **atom** (content binds `owner ‖ root ‖ digest ‖ z`) |
| the z-order (paint order) | the **order relation** (chained `Add` edges; the walk = the paint order) |
| the active tab | a single-valued **field** `"active_tab"` (a `SetField`) |
| the focus holder | a single-valued **field** `"focus"` (a `SetField`) |
| a minimized surface | a **tombstoned** atom (off the walk, kept in the graph — Pijul alive/dead) |
| the whole workspace | a **document** committed by `substrate_commit` (the real heap root) |

The projection is built by **applying an ordinary `Patch`** (`Add`/`SetField`) — a
desktop layout is authored by *exactly* the document grammar a prose edit uses.

**What it unlocks (each is a document affordance, now applicable to the desktop):**

- **Shareable + light-client-checkable.** A desktop layout has a real commitment
  (`desktop_commit` = the sorted-Poseidon2 heap root). Two parties agree they see
  the same desktop **iff** the root matches; a window that lies about which cell it
  is (a forged `owner`) changes the root — the document's **anti-forge tooth,
  inherited** (test: `a_forged_surface_owner_changes_the_commitment`).
- **Rehydratable + diffable.** A desktop is a value you can serialize, send, and
  re-fold; a layout change is a *document diff* (test:
  `a_rearranged_desktop_has_a_different_commitment`).
- **Branchable + time-travellable.** Wrapped in a `History`, a layout edit is a
  recorded patch; `History::replay_to(tip)` re-hydrates a past desktop; a
  `branch`/`Stitch` forks an alternate arrangement in a *confined virtual branch*
  (the `branch_stitch` organ) and reconciles the good parts back.
- **Conflict-as-state = the firmament dual of T3.** The compositor's T3 gate
  *refuses* a scene with two focus flags (`PresentError::DoubleFocus`). Because the
  focus + active-tab are *single-valued fields*, the document reading does the
  **dual**: two devices each claiming focus on a different surface do NOT
  clobber — the clash is a **first-class `Regime::Field` conflict**, each claim
  attributed to its device, resolved later by an explicit superseding patch (never a
  silent loss). This is the *right* semantics for the multi-device "one cap across
  distance" case, where two devices legitimately diverge and reconcile (test:
  `two_devices_contending_focus_is_a_first_class_conflict_not_a_clobber`).

**The reflexive loop closes.** A layout edit authored as a `SetField` patch on the
desktop-document is the document *editor* editing the document that IS the desktop;
on the substrate that patch's executor cut-over rides `WorkspaceCell::commit`
(already a real `Effect::SetField` turn), so authoring the desktop-document is a
witnessed turn leaving a receipt — the document language editing its own host.

**Prototyped (standalone, green, this work):** `dregg-doc/src/desktop.rs` (gated on
`substrate`, beside `substrate.rs`) — `DesktopSurface`, `scene_to_doc`,
`desktop_commit`, `render`, `tombstone_surface`, `set_active_tab`, `resolve_focus`,
with 8 both-polarity tests against the **real `substrate_commit`** (`lake`-free,
`cargo test --features substrate desktop::` → 8/8 green). The cockpit adapter
`starbridge-v2/src/desktop_doc.rs` (gated on `embedded-executor`, beside `doc_lens`)
maps the live `CompositedSurface`/`WorkspaceCell` onto that verified core (wired in
`starbridge-v2/src/lib.rs`, gated on `embedded-executor`).

**The COMPOSED reading (the reflexive weld, this work):** the flat projection above
reads the desktop as TEXT atoms. `dregg-doc/src/composition.rs §6` welds it to the
`Op::Embed` algebra instead: `DesktopSurface{owner: CellId, z_layer, focus_flag}`,
`scene_to_composed` (each window an `Op::Embed` of its owner cell, chained in paint
order — `Pin::Live`), `workspace_resolver` (the per-window child-cell resolver), and
`close_surface` (`Op::Remove`). The desktop becomes a *graph of cells* that folds
through the SAME `content_composed`, so it inherits the per-viewer membrane, the
forkable layout pushout, and the cycle guard. Both polarities bite against the REAL
fold (not a fixture): the live workspace projects + round-trips
(`the_workspace_projects_to_a_composed_document_that_round_trips`), a close edit
drives a real desktop change (`editing_the_projected_document_drives_a_real_workspace_change`),
an out-of-cap window DARKENS through the membrane
(`an_out_of_cap_window_darkens_in_the_composed_desktop`), and two devices opening
windows merge as a layout pushout with a first-class fork
(`two_devices_each_open_a_window_merge_as_a_layout_pushout`). 14/14 module tests +
4/4 crate-boundary integration tests (`dregg-doc/tests/desktop_as_composed_document.rs`)
green, standalone (`cargo test --no-default-features composition`).

---

## 7. SPECULATIVE / OPEN (honestly flagged)

- **Cycle prevention.** A composed document is a *graph* of cells; nothing yet
  forbids `A` embeds `B` embeds `A`. The render must detect cycles (a visited-set
  on `CellId`, like the existing `content` walk's `visited` on `AtomId`) and
  surface a cycle as a first-class *state* (`ChildResolution::Cycle`), never a
  stack overflow. The prototype includes the visited-set guard; whether a cycle
  is ever *legitimate* (a mutually-recursive document?) is open — start by
  forbidding it, relax if a real use wants it.
- **Live-embed liveness-typing.** A `Pin::Live` embed's rendered bytes are
  whatever the child committed at render time — so a composed document's content
  is only as "finalized" as its least-finalized live child. The `Rehydration`
  liveness-type (`rehydrate.rs`) should propagate: a document with a `Virtual`
  live child is itself `Virtual` at that region. This is the honest extension of
  "the system cannot lie about whether you're reading published or draft" to the
  composition tree. Named, not prototyped.
- **Layout vs flow.** `EmbedRole` is a coarse first cut (Section / Figure /
  Inline / Block / Citation). Real layout (sizing, float, columns) is a render
  concern, not an algebra concern — it belongs in the servo render-pass
  (`DOCUMENT-LANGUAGE.md` §4.3), not in `dregg-doc`. The algebra commits only to
  *which cell goes where in the order*; *how* it lays out is the renderer's. Do
  not pull layout into the patch core.
- **The granularity of the child.** A child cell can be as coarse as a whole
  appendix or as fine as a single equation. The §4.4 atom-granularity question
  recurs at the cell level: *what is the unit of composition?* A design choice to
  make empirically — start coarse (a section is a cell), refine if real authoring
  wants finer (a sentence is a cell) — not a theorem.
- **Joint layout edits.** Two parties co-placing an embed atomically (a contract
  where both must agree the clause cell goes here) is a joint-turn
  (`FamilyBinding`) on the parent — the partial-turn-with-holes shape
  (`partial-turn-promises`). Named; the existing joint-turn machinery carries it.
- **Transclude-from-an-embedded-child.** Composition and transclusion *compose*:
  an embedded child may transclude a value from a fourth cell. The algebra is
  closed under this (the resolver recurses; transclusion is a value the child's
  render already resolves), but the *commitment* interaction (does the parent bind
  the transitive transclusion?) wants the same separate-verification discipline
  as §3.3 — likely: no, the parent binds its embed pointers, each child binds its
  own transclusions, the checks compose. Worth a Lean lemma; flagged speculative.
- **Namespace rebind authority + the `Name`-embed trust surface.** A `Name` embed
  delegates *which cell renders here* to whoever holds the namespace cell's `edit`
  cap. That is exactly the point of the binding arm (the role's owner curates the
  binding), but it is also a trust surface a `Cell` embed does not have: a
  malicious/compromised namespace can rebind a name to a hostile cell, and every
  `Name(name)` embed of it follows. The mitigations are already in the substrate
  and want wiring, not invention: (a) pin a `Name(uri, At(r))` when you want the
  binding's curation but not its future mutation (the name resolves once, the
  version is frozen — §2.1b last row); (b) the rebind is a witnessed turn on the
  namespace cell, so it leaves a receipt and is itself attenuable/governable
  (the governed-namespace route-table is the threshold-gated form); (c) the
  embed's commitment binds the *name + namespace* (§5.7), so a light client can
  see *which* namespace it trusts. The open design choice is the default trust
  posture (live-follow vs pin-by-default for `Name` embeds across a trust
  boundary) — a policy, not a theorem; flagged.

---

## 8. HONESTY LEDGER

**Read at HEAD for this doc (read-only):** `dregg-doc/src/{lib,atom,graph,patch,
content,merge,regime,history,doc,commit,substrate}.rs` (the full patch core —
the `DocGraph` of `Atom{content: String, status, provenance}` + order-edges +
field store; `Op::{Add,Delete,Connect,SetField}`; the union pushout `merge`; the
antichain `ConflictRegion`; the provenance-binding `commit`/`substrate_commit`
with the anti-forge tooth); `metatheory/Dregg2/Deos/Transclusion.lean` (the
verified field-VALUE quote — `ImportedEq`, the four proven Xanadu properties);
`starbridge-web-surface/src/{transclusion,web_of_cells,rehydrate}.rs` (the
`TranscludedField`, `DreggUri`/`CellId` `dregg://` addressing, `AttestedResource`
verification, `Membrane::project`); `starbridge-v2/src/web_cells.rs` (the
`{view,comment,edit,admin}` affordance surface, the powerbox-upgraded
`SemiReinteractiveTransclusion`, the per-viewer darkened span). **Confirmed:**
there is **no embed/cell-composition op today** — an atom carries a `String`;
transclusion imports a *value*, never a *cell*. The composition operator is
genuinely new; the substrate it rides (`dregg://` addressing, the membrane, the
cap surface, the patch core) is all built.

**Prototyped (standalone, `cargo test`-able, this work):** `dregg-doc/src/composition.rs`
— `Op::Embed`, `AtomContent::{Text,Embed}`, `ChildRef`/`Pin`/`EmbedRole`, the
`ChildResolver` trait + in-memory `MapResolver`, `content_composed` (the recursive
membrane-gated fold), `merge_composed` (the product-of-pushouts), the
pin-divergence conflict, the cycle guard, and the per-viewer darkening
(10 in-module tests). Kept self-contained (it does not perturb the existing
`Atom`) so it is *additive*.

**Binding-vs-identity extension (standalone, green, this work):** the same
`composition.rs`, with `ChildRef` grown to the **two-arm**
`Cell(CellId, Pin) | Name(DreggUri, Pin)` (§2.1b), `DreggUri`, the
`NamespaceResolver` trait + in-memory `MapNamespace`/`NoNamespace`, the resolver's
name-resolution step (`resolve` resolves `Name`→`CellId` via the namespace, THEN
the cell), and `ChildResolution::Unbound`. The two arms' properties are proven
both-polarity in `dregg-doc/tests/composition_binding.rs` (4 tests, green):
EMBED-FOLLOWS-REBIND (`name_embed_follows_a_rebind_but_a_cell_embed_does_not` —
the `Name` follows, the `Cell` does not; `…unbound…heals…`), EMBED-SURVIVES-ROTATION
(`a_cell_embed_survives_the_identity_cells_key_rotation` — id stable across
rotation, with the current-key-bound counterfactual exhibited as the broken world
the substrate is NOT), and the NO-ROT corner
(`a_pinned_embed_resolves_the_frozen_past_even_after_the_source_is_retired` — a
`Pin::At` survives retirement, a `Pin::Live` dangles). The identity-cell-id
stability finding (§3.5) is the load-bearing fact established by census.

**Named wiring (NOT edited into shared lib.rs/Cargo beyond the module
declaration — reported):**
- `dregg-doc/src/lib.rs` — `pub mod composition;` (the module declaration that
  makes the prototype live + the integration test reach it; this one line was
  added so the 14 tests run — without it the module is dead code). Re-exports
  (`pub use composition::{…}`) are NOT added; the integration test reaches the
  `pub` items via the `pub mod`.
- The `COLL_EMBEDS` leaf in `substrate.rs::to_heap_map` (per §5.7, two-arm).
- The substrate `NamespaceResolver` over the `WebOfCells` nameservice (per §5.8).
These touch shared/feature-gated files; per the build discipline they are
reported, not edited.

**The substrate-backed resolver — LANDED (§3.4, sibling work):**
`starbridge-v2/src/cell_transclusion.rs` realizes the concrete `ChildResolver` over
`WebOfCells` + `Membrane` + `AffordanceSurface` that this ledger first named as a
residual: `WholeCellTransclusion::{embed, project_for, reshare_to, rehydrate_embed}`
+ `EmbeddedCellView::{Visible, Darkened}` (the concrete `ChildResolution`) +
`ComposedCellDocument::resolve_for` (a document composed from whole cells, resolved
per-viewer). gpui-free, `cargo test`-able beside `web_cells.rs`; both-polarity teeth
(see-at-cap-level / over-reach-darkens / reshare-amplification-refused). Read at HEAD
for it: `starbridge-web-surface/src/{transclusion,rehydrate,affordance,delegate}.rs`
(`TranscludedField`, `Membrane`, `AffordanceSurface::project_for`, `SurfaceCapability`)
+ `metatheory/Dregg2/Deos/{Surface,Membrane,Transclusion}.lean` (the whole-cell-as-cap
+ reshare-non-amp + Xanadu proofs). The wiring (`pub mod cell_transclusion;` gated on
`embedded-executor`, beside `web_cells`) is **WIRED** in `starbridge-v2/src/lib.rs` —
the resolver ships in the embedded-executor library, no longer a dead untracked file.

---

*( ⌐■_■ ) a closing couplet, since a document turned out to be a tree of cells:*

*a section owned by other hands, a figure not your own —*
*compose the whole, and each cell stands, conflicting on its own.*
