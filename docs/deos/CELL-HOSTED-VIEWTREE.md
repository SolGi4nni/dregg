# Cell-hosted view-trees — the composition keystone (a cell HOSTS a view-tree; a tree MOUNTS a cell)

The framing, stated once and held throughout: **a cell is not the leaf of the DOM — it is a
first-class hostable component whose committed heap STORES its own evolving view-tree, and
which any tree can MOUNT whole as a subtree at any level.** Today `bind` treats a cell as an
atom: the tree reads one scalar value off `(cell, slot)`. That is backwards for composition.
The right model inverts it: the cell is ABOVE the view-tree it hosts; the view-tree is the
cell's committed state; and a hosted tree itself contains mounts of OTHER cells → fractal
recursion (cells-host-cells-host-view-trees, to arbitrary depth). This is MORE fundamental
than `section`/`tabs`/`gauge`/`divider`: those are shapes WITHIN one cell's tree; `host` is
how one cell's whole tree composes INTO another's.

Why it is now possible: umem landed (umem IS the deployed prover). A cell has its own
committed, witnessed heap (`CellState.heap_map`, the sorted-Poseidon2 `(collection, key) →
felt` map digested by `heap_root`). So a cell can STORE its serialized view-tree there,
mutate it via receipted verified turns, and be transcluded whole — the UI becomes the cell's
verified state, recursively. The storage mechanism already exists and is proven: the
program-in-cell weld (`deos-js/src/portable.rs`) chunks an arbitrary blob across heap
collection `PROGRAM_COLL` (31 payload bytes per `FieldElement` leaf, key 0 a length header).
Cell-hosted view-trees reuse that exact mechanism under a distinct collection.

---

## 0. The three distinct read primitives (host is NOT bind, NOT value-transclude)

| primitive | what it reads | from where | grain |
|---|---|---|---|
| `bind{slot}` | ONE scalar value | the applet's cell, model slot | a leaf value |
| value-`transclude` (today) | a value/snapshot | another cell | a leaf value |
| **`host{cell}` (this)** | an ENTIRE view-tree | the hosted cell's committed **heap** | a whole subtree |

`bind` makes a cell an atom (a number on screen). `host` makes a cell a COMPONENT (its whole
self-described surface, mounted as a subtree). The hosted subtree is sourced from the cell's
heap, not from the parent — the parent tree does not own or author it; it references it.

---

## 1. The `host` / `mount` node and the cell-heap-as-view-source model

### The node (pure data, `deos-view/src/tree.rs`)

```rust
ViewNode::Host {
    cell: String,                    // the hosted cell's id (hex) — the mount reference
    view: Option<Box<ViewNode>>,     // the resolved hosted view-tree; None = unresolved mount
}
```

Wire shape: `{ kind:"host", props:{ cell:"<hex cell id>" }, children:[ <0-or-1 subtree> ] }`.

- **Unresolved mount** (`children:[]` → `view: None`): a bare reference to a cell. The
  renderer paints an honest `‹mount cell …: unresolved›` placeholder until a resolver fills
  it from the cell's heap (the same honest-degradation idiom as the `‹unmapped node›`
  fallback). This is the canonical authored form: `deos.ui.host(cellId)`.
- **Provided / pre-baked mount** (`children:[subtree]` → `view: Some`): the hosted subtree
  carried inline. This is the "provided sub-tree source" first cut and the serialized form a
  resolver emits once it has read the heap.

`host` stays PURE DATA — it carries a cell-id STRING and (optionally) a resolved subtree, no
live `Applet`/`Ledger`/`Cell` handle. That is load-bearing: the `web` and `discord` renderers
are gpui-free AND deos-js-free (serde/serenity only), so the IR cannot reach into a heap. The
heap read happens OUTSIDE the IR, in a resolver at the boundary (below), and the result is
spliced back in as `view: Some(...)`. Every renderer then walks the SAME resolved data.

### The cell-heap-as-view-source (native, `deos-view/src/mount.rs`)

A cell stores its view-tree as a **heap blob** under collection `VIEWTREE_COLL` (`0x1E4F`),
disjoint from `PROGRAM_COLL`. The bytes are the canonical `{kind,props,children}` JSON the
engine already `JSON.stringify`s — so the stored substance is exactly what `parse_view_tree`
reads. The codec is the proven chunked-heap-blob (mirroring `portable.rs::write/read_program_blob`):
key 0 = the byte-length header; keys `1..` = 31-byte payload chunks (leaf byte 0 = fill length).

- write: `write_view_blob(cell: &mut Cell, json: &[u8])` — committed by `heap_root` (the
  view-tree becomes part of the cell's committed state, travels with `to_cell_bytes`).
- read: `read_view_blob(cell) -> Option<Vec<u8>>`, and
  `view_tree_from_cell_heap(ledger, cell_id) -> Option<ViewNode>` (read + `parse_view_tree`).

Staying live: the resolver re-reads the cell's heap on demand. A receipted edit to the cell's
hosted tree (§3) moves the cell's `heap_root`; the host re-resolves and `set_tree`s the
reshaped subtree — the same fine-grained "a turn moved the source, re-read it" loop `bind`
already uses, lifted from a scalar slot to a whole subtree.

---

## 2. Fractal recursion + cycle-safety (the recursion contract)

A hosted tree may itself contain `host` nodes → arbitrary depth (cells-host-cells). The
resolver (`resolve_mounts`, pure data in `tree.rs`) walks a tree against a `MountSource`
(`hosted_tree(cell) -> Option<ViewNode>`, with a blanket impl for any `Fn(&str)->Option<ViewNode>`
and a `MapMountSource` for in-memory sources):

```rust
pub fn resolve_mounts(tree: &ViewNode, source: &dyn MountSource) -> ViewNode;
pub const MAX_MOUNT_DEPTH: usize = 16;
```

The recursion contract, fail-safe by construction:

1. **Acyclic depth bound.** The resolver carries the path of cell-ids currently being mounted
   (a visited stack) and a depth counter. At `MAX_MOUNT_DEPTH` it stops and paints a
   `‹mount depth exceeded›` body — a huge-but-acyclic tree can never blow the stack.
2. **Cycle detection.** If a `host{cell}` names a cell already on the visited path (a cell
   hosting itself, or an a→b→a mount cycle), the resolver stops and paints a
   `‹mount cycle: <cell>›` body INSIDE the host frame (the cell is still shown; only the
   self-reference is cut). Bounded, fail-safe, never an infinite unfold.
3. **Source miss.** A `host{cell}` whose cell the source cannot supply stays `view: None` and
   paints the unresolved placeholder — honest, never a crash.
4. **Provided subtrees recurse too.** A pre-baked `view: Some` is still walked for nested
   hosts, so an inline-carried subtree composes identically to a heap-sourced one.

This is the same shape as `transclude` cycle-safety, generalized: the unit of the cycle is a
cell id, and the bound is on the mount DEPTH, not the node count.

---

## 3. Evolution = receipted turns (the living verified object)

A cell's hosted view-tree is not a static asset — it is mutated by VERIFIED TURNS, exactly
like any other cell state. The edit-from-within path already in place
(`deos-js/src/card_editor.rs` `ViewPatch` + `starbridge-v2/src/dock/card_surface.rs`
`ModeCardSurface::edit_view`) applies a `ViewPatch` (`AddButton`/`AddText`/`AddBind`/`Relabel`)
to a card's view-tree as a receipted, blamed patch and `set_tree`s the live surface. For a
cell-hosted tree this becomes: the patched view-tree is re-serialized and written back into
the cell's heap (`write_view_blob`) so the new tree is committed by `heap_root` and carries a
receipt. The host then re-resolves and the parent's rendered subtree changes.

The surface is therefore a LIVING verified object: every shape it takes is a committed cell
state with a receipt and blame; replay re-derives it; a light client witnesses the
`heap_root` move. The honest seam: the heap-write today happens at the genesis/`with_cell_mut`
seam (as `portable.rs` writes the program blob) — a first-class `Effect` that writes a
view-tree blob into the heap (so the blob-write IS the turn's effect, not an out-of-band
mutation alongside it) is the named follow-up that closes "the ViewPatch write is itself the
receipted turn" end-to-end. The READ path (heap-as-source) is fully real today.

---

## 4. The reflective-cockpit payoff (it falls out)

A cockpit surface IS a cell hosting its own view-tree. The cockpit mounts it with one
`host{surfaceCell}` node; the renderer reads the surface's tree from the cell's heap and
paints it. The confined agent inhabiting the cockpit rewrites the surface by applying a
receipted `ViewPatch` into that cell's heap (§3) — the host re-resolves, the surface
reshapes, and the rewrite is a committed, blamed, replayable turn. The whole reflective loop
(REFLECT-on: read the cell's hosted tree; REWRITE: receipted ViewPatch into the cell's heap)
is just §1 + §3 composed. Fractal recursion means a surface can host sub-surfaces (each its
own sovereign cell) and the agent can rewrite at any level — the cockpit is one tree of
mounted cells, sovereign all the way down.

---

## 5. The bind-cursor / renderer-independence invariant through `host`

The tree-walk (pre-order) bind cursor invariant (every renderer + `bind_plan` visit `Bind`
nodes in identical order, so the Nth `Bind` is `BindingId(n)`) is preserved through `host`:
a `host`'s resolved `view` is recursed at the host's position by EVERY renderer
(`render.rs` `node` + `bind_plan`, `web.rs` `node`, `discord.rs` `block`/`inline`) in the
same order; an unresolved host (`view: None`) consumes no cursor positions in any renderer,
so it cannot desync them. All four renderers walk into the hosted subtree consistently — the
card stays renderer-independent across native/web/discord by construction.

A deeper concern named for the follow-up: in the single-cell `AppletView` a hosted subtree's
`bind`s currently re-read the PARENT applet's cell slots; a true multi-cell binding (each
hosted subtree bound to its OWN child cell's ledger) is the natural next rung. The structural
cursor invariant above holds regardless; the multi-cell ledger binding is the enrichment.

---

## 6. The first cut implemented (this change)

- `ViewNode::Host { cell, view }` + `RawProps.cell` + `RawNode::lift` (`host` → `view` from
  the first child, else `None`), in `deos-view/src/tree.rs`.
- `MountSource` (+ `Fn` blanket impl + `MapMountSource`), `MAX_MOUNT_DEPTH`, and
  `resolve_mounts` (visited-stack cycle detection + depth bound) in `tree.rs`, with pure-data
  unit tests: fractal 2-level resolve, self-cycle, mutual cycle, depth bound, provided-subtree
  passthrough.
- The `host` arm in ALL FOUR renderers (`render.rs` `node` + `bind_plan`, `web.rs` `node` +
  CSS, `discord.rs` `block` + `inline`) — a bordered/framed host container with a `⌂ <cell>`
  header wrapping the hosted subtree, or the honest unresolved placeholder.
- `deos-view/src/mount.rs` (native): `VIEWTREE_COLL`, `write_view_blob`/`read_view_blob`
  (the proven chunked-heap-blob codec), and `view_tree_from_cell_heap` — the real
  heap-as-view-source READ path.
- A native render proof (`deos-view/tests/mounts_a_hosted_subtree.rs`): a parent card mounts a child
  cell's heap-stored hosted view-tree as a subtree and renders it nested (the child's tree
  appears inside the parent), proves a FRACTAL 2-level nest (child hosts grandchild, both
  heap-sourced), and a receipted edit to the child's hosted tree re-resolves into a changed
  rendered subtree (the frames differ).

The remaining rungs: the heap-write `Effect` (so the ViewPatch write IS the turn's effect),
the multi-cell `AppletView` ledger binding (§5), and `deos.ui.host` in the JS prelude.
