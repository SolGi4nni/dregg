# UNIVERSAL MEMORY — one Blum multiset for all of dregg's state

*(the deepest table-collapse question, answered in Lean: `metatheory/Dregg2/Crypto/UniversalMemory.lean`.
Sits on `Crypto/MemoryChecking.lean` (Blum) and `Substrate/Heap.lean` (the openable sorted map).
Lean/design layer only — no circuit Rust rides this document.)*

## The question

`EPOCH-DESIGN.md` gives five tables: main · poseidon2 chip · range · **memory** ·
**map-ops**. The memory table already carries registers, heap ops, cap checks and
nullifier touches as one read/write multiset. The universal-memory thesis pushes
one step further: make the four map roots (cap_root, nullifier_root, heap_root,
index root) **derived boundary views** over the final memory cells, so the
architecture is

    main + chip + range + ONE memory table,
    with the boundary-root derivation absorbed into map-ops
    (5 consistency arguments → 1 interior argument + boundary reconciliation).

Is that sound?

## The verdict: SOUND — proved, with the boundary conditions named

### Interior: one balance covers every domain — `universal_memory_sound`

The unified address is `(domain, key)` — abstractly `Domain × κ`, concretely
`addr = hash[domain_tag, collection_id, key]` (CR makes the concrete form
injective, i.e. exactly the pair). `Domain ∈ {registers, heap, caps, nullifiers,
index}`; a future state component is a new domain value, never a new table.

**`universal_memory_sound`**: nodup declared addresses + address closure + the
per-op serial discipline + the ONE multiset balance (`MemCheck`, one
LogUp/grand-product argument) imply

1. the whole unified trace is consistent (`memcheck_sound`, inherited), and
2. **every domain's projection, stripped of its tag, is a consistent standalone
   memory** from that domain's slice of the initial state.

The two workhorses are pure semantics, no multisets:

* `consistentFrom_filter` — consistency restricts to any address class (ops
  outside the class never move the class's cells);
* `consistentFrom_strip` — on a single-domain trace the tag peels off
  injectively (`(d,a) = (d,b) ↔ a = b` is the whole content).

So one memory argument soundly covers registers + heap + caps + nullifiers +
index simultaneously, with **zero intra-proof hashing**. Note the per-domain
guarantee is delivered semantically (consistency of the projection), not as a
literal per-domain `MemCheck` — filtering a trace breaks serial contiguity, so
the right statement is the semantic one, and it is the one apps need.

The domain tag is **load-bearing**, witnessed both ways in the module's guards:
a cross-domain tuple-steal (a nullifier read claiming a heap write's tuple)
unbalances the multisets, and the *flat untagged* address space genuinely
aliases — a cap check at key 7 reads the nullifier-domain value at 7 (a ghost
capability is *consistent* in the flat space, and the honest absence read is
refused).

### The final column is forced — `memcheck_pins_final`

The boundary derivation reads the prover's claimed final tuples. Those claims
are pinned: under the balance + discipline, every declared address's final
value **equals the genuine fold of the trace** (`chains_pin_fold`, the
value-twin of `consistentFrom_of_chains`). The boundary view is derived from a
forced column, not a chosen one.

### Boundary: the map roots are derived views — `boundary_root_derived`

A map domain stores `Option ν`: `some v` = present cell, `none` = absent. The
derived view `boundaryCells` is the present final cells over the declared
addresses in sorted order — literally a sorted leaf list in `Substrate/Heap`'s
sense (`boundaryCells_sorted`, `get_boundaryCells`).

**`boundary_root_derived`**: if today's committed map and the final memory's
domain view agree as lookups, their `Heap.root`s are EQUAL — by canonicity
(`ext_get` / `root_deterministic`), **no crypto hypothesis**. And
**`boundary_root_from_memcheck`** welds it to the balance: the root derived
from the prover's claimed final column equals the root of the genuine
post-state map. Materializing roots at the boundary changes *where* the
commitment is computed, never *what* it commits to: **a refactor, not a
semantic change**. Heap_root and the nullifier root are immediate instances
(their leaf shape is `hash[addr, value]`, exactly `Heap.leafOf`).

### THE NULLIFIER WIN — `nullifier_fresh_sound`: YES, Merkle-path-free intra-proof

Nullifier cells are insert-only (`InsertOnlyAt`: every write installs `some _`
— nobody un-spends). Then **one read row returning `none`** at
`(nullifiers, x)` — certified by the same single balance as everything else —
proves:

1. `x` was absent from the proof's **initial** nullifier view, and
2. no earlier op in this proof inserted `x` — **intra-proof double spends are
   impossible** (the lying "still fresh" read after an insert is refused under
   every possible final claim; guard-witnessed).

Freshness = "this address was never written in the nullifier domain": a memory
property. **No Merkle path, no gap opening, no hashing intra-proof.**
Cross-proof persistence rides the boundary: `nullifier_fresh_binds_root` loads
the initial view from the committed map and composes with `root_injective` —
the published root pins absence in ANY heap claiming it. The sorted-tree
machinery (`sorted_gap_excludes`, `NonMembership.lean`) survives exactly at the
boundary, authenticating the loaded initial view against the incoming root —
**once per touched address per proof, never per access**.

## What stays separate

* **Move's conservation.** The memory argument is per-address (rectangular).
  `Calculus/BiorthTensor.lean` proved conservation is NOT expressible by any
  rectangular/per-component family (`conservation_not_behaviour_rectangular`,
  the generic mix law `rect_mix_in_biorth`); Σδ=0 needs the **correlated pair**.
  Conservation stays an in-row paired-write constraint on the move row — it
  cannot ride the multiset, by theorem, not by taste.
* **The chip and range tables.** Hash sites and limb discipline are lookup
  relations, not state accesses; untouched by this collapse.
* **The receipt index's boundary form.** The index domain projects consistently
  like any other (the keystone is domain-uniform), but its boundary commitment
  is the MMR root (`Lightclient/MMR.lean`, `mroot_injective`), not a sorted
  map root. The interior claim covers it; the `boundary_root_derived` analogue
  for the MMR (mroot of the address-ordered final cells) is stated here as the
  remaining derivation case, not proved — the MMR module already binds the log,
  so this is an adapter lemma, not a soundness gap.

## The honest obstructions (each named, none fatal)

1. **Boundary reconciliation per proof.** The initial values of touched
   addresses must be authenticated against the incoming roots, and the final
   cells folded back into outgoing roots. That is today's map-ops machinery
   verbatim — the collapse moves authentication from per-touch to
   per-boundary-reconciliation; repeated intra-proof touches of the same cell
   are free. The win is real but it is "per-touch → per-touched-key-per-proof",
   not "zero hashing anywhere".
2. **Coverage for derived roots.** `boundary_root_derived`'s hypothesis is that
   the declared addresses cover the domain's live cells (the map holds exactly
   the declared finals). In the touched-only regime the outgoing root is
   instead produced by per-key map-op updates (today's sorted-insert gates);
   the derivation theorem is the semantic anchor that both regimes commit to
   the same object.
3. **The live cap-leaf shape.** Today's cap leaf is
   `hash[holder, target, rights, op]` (`EffectVmEmitCapRoot.siteCapEdgeLeaf`),
   not the generic `hash[addr, value]`. The agreement is proven at the
   `Substrate/Heap` layer (the R2-established generalization of the cap_root
   machinery); pulling the live leaf shape under it is the named adapter case
   (encode the cap tuple as the cell value — value-codec lemma, no new
   combinatorics).
4. **Address-space hashing at the boundary.** `addr = hash[domain_tag, coll,
   key]` puts one chip lookup per *distinct touched address* per proof (to bind
   the tag), against the four separate trees' per-access path hashing today.
   For any trace touching an address more than zero times, the unified form is
   no worse; for hot addresses it is strictly cheaper.

## File map

* `metatheory/Dregg2/Crypto/UniversalMemory.lean` — everything above:
  `Domain`/`UAddr`, `universal_memory_sound`, `chains_pin_fold` /
  `memcheck_pins_final`, `boundaryCells` + `boundary_root_derived` +
  `boundary_root_from_memcheck`, `InsertOnlyAt` + `nullifier_fresh_sound` +
  `nullifier_fresh_binds_root`; non-vacuity both polarities on concrete
  five-domain traces; `#assert_axioms` ⊆ {propext, Classical.choice,
  Quot.sound} throughout (crypto only as the named `Poseidon2SpongeCR`
  hypothesis, in the one root-binding composition).
* Foundations: `Crypto/MemoryChecking.lean` (`memcheck_sound`),
  `Substrate/Heap.lean` (`ext_get`, `root_deterministic`, `root_injective`),
  `Crypto/NonMembership.lean` (`sorted_gap_excludes` — now boundary-only for
  nullifiers), `Calculus/BiorthTensor.lean` (why conservation stays out).
