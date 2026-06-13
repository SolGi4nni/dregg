# rbg → seL4 — from "Robigalia ideas in std Rust" to a real seL4 component

`docs/SEL4-EMBEDDING.md` §0 is honest that `rbg/` is **heritage, not a host**:
it ports Robigalia's *userspace design ideas* (the VFS triple, directory cells,
scoped intents, factory-constrained creation) into ordinary `std` Rust on the
dregg runtime, with **no seL4 syscall, no CapDL, no capability-to-kernel-object
binding** anywhere. `rbg` depends only on `blake3`, `dregg-types`, `dregg-cell`.

This note sketches the **concrete first step** from those ideas toward real seL4
primitives: which rbg concept maps to which seL4 object, and what the minimal
first port actually is.

## The conceptual mapping

| rbg concept (heritage, `std`) | seL4 primitive | What the port actually does |
|---|---|---|
| `DirectoryCell` — a c-list (capability list) of named entries, versioned, with provenance | **CNode** (a kernel-managed capability table) + a userspace name→slot index | The directory's c-list becomes a real seL4 CNode; entries are caps in CNode slots; the name→slot map stays in userspace (seL4 caps are slot-indexed, not named). |
| `SturdyRef` — a persistable, re-vivifiable reference to a cell | **Badged endpoint cap** + a CapDL/DreggDL entry that re-mints it at load | A SturdyRef is the dregg analogue of a CapDL "cap with a badge"; reviving it = the loader re-installing the badged cap from the deployment spec. |
| `ScopedIntentPool` — intents bounded by directory membership | **Endpoint cap whose badge encodes the scope** | The "scope" becomes the badge value on the endpoint the intent is sent through; seL4 enforces that only badge-holders can invoke it — membership-bounding by construction. |
| `DirectoryFactory` / `directory_factory_descriptor` — constrained cell creation | **Untyped memory cap + the `seL4_Untyped_Retype` invocation** | The factory's "may only create this shape" caveat maps to: the factory PD holds an Untyped cap and the retype template; it can only mint objects of the declared type — the seL4-native form of the slot-caveat enforcement. |
| `vfs::Volume` (budget) / `Blob` (content-addressed note) / `Directory` | **Frame caps** (Blob = a page) + the `persist` PD's block cap (Volume = a budget of frames) | Content-addressed notes ("the address IS the content") need no inode/naming layer — exactly the property that lets a minimal block-cap backend suffice (§3.3). A Blob is a frame; a Volume is a quota of frames the `persist` PD owns. |
| `MetaDirectory` (registry-of-registries) | **A root CNode whose slots are sub-directory CNode caps** | The yellow-pages registry becomes the root task's CNode holding caps to each component's CNode. |
| `TopicSubscriptionManager` (gossip-topic audience bounding) | **Notification caps, one per topic, badged by audience** | A subscription is a notification cap; the audience bound is the badge; the `gossip` PD signals subscribers via their notification caps. |

## The concrete first step (the smallest real port)

The smallest thing that turns an rbg *idea* into a real seL4 *mechanism* is the
**factory → Untyped retype** edge, because it is the one place where dregg's own
"capability-secure creation" claim becomes a kernel-enforced fact:

1. **Pick `directory_factory_descriptor`** (`rbg/src/factory.rs`) — it already
   declares a slot layout + creation caveats in `FactoryDescriptor` shape.
2. **Give the factory PD an Untyped cap + a retype template** in `dregg.system`
   (a `<memory_region>` of untyped memory mapped only to that PD).
3. **Replace the std `DirectoryFactory::create`** with a seL4 invocation:
   `seL4_Untyped_Retype(untyped, CNode_object, ...)` mints a fresh CNode for the
   new directory's c-list. The factory *physically cannot* mint anything but the
   declared type — the slot-caveat is now a kernel invariant, not a Rust check.
4. **The DreggDL/CapDL bridge** (§6 of the embedding doc): the directory's
   initial cap layout is written once in a DreggDL spec; a loader instantiates
   it, exactly as CapDL instantiates seL4 component caps. This is where
   "capabilities all the way down" becomes reproducible: the seL4 CapDL spec
   for the component caps, the DreggDL spec for the cell caps.

This first step is *additive* — it does not require the Lean runtime port, so it
can proceed in parallel with the §2 blocker. It earns the "capabilities all the
way down" claim for the `persist`/factory path before the full executor PD
exists.

## What this is NOT (yet)

- There is no rbg code change here — this is the *design bridge*, and the first
  port (`DirectoryFactory` → Untyped retype) belongs in `verifier-pd/`'s sibling
  `factory-pd/` once the rust-sel4 toolchain is wired. rbg stays the std-Rust
  design sketch; the seL4 component is a new crate that *uses* rbg's descriptors.
- No seL4 syscall is exercised in this repo today (no toolchain). The mapping is
  the reviewable artifact; the invocations above are the recipe.
