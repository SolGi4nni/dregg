# C9 — the FIRST RECLAIMING allocator: a fixed-size-block LIFO FREELIST with a proven PARTITION invariant, Link-A-proven that `alloc`/`free` PRESERVE it and free-then-alloc HANDS BACK the freed block (memory REUSE)

**Date:** 2026-07-05 · **Machine:** hbox (i9-12900) HOL4/CakeML; drorb (Lean) model kernel.
**Status: DONE — the C7/C8-named `free/reclaim` core is OPENED (its first honest
step).** One HOL4 theory (`hol-c9/arenaFreelistLinkAScript.sml`), 8 kernel-checked
theorems, **every one `[oracles: DISK_THM] [axioms: ]`, `axioms
"arenaFreelistLinkA" = 0`, zero `cheat`/`new_axiom`/`mk_thm`/oracle in source.**
Clean rebuild `arenaFreelistLinkATheory [1/1] OK` in ~6 s on the C2–C8 chain. The
emitted Pancake compiles with `cake` (exit 0), links, and RUNS — a freed block
address is HANDED BACK OUT by the next allocation, byte-exact.

## The residual C7 and C8 both named, and what C9 opens

C7 (bump, fixed + general-N) and C8 (the variable-length collector) both closed
the entire **forward** allocation story and named the *same* irreducible residual
verbatim:

> *"No free / reclaim.  The bump pointer only advances.  A verified allocator with
> `free`, a freelist, coalescing, or fragmentation reasoning is NOT modelled and
> IS still open research."*

**C9 takes the smallest honest bite of exactly that:** fixed-size blocks + a LIFO
freelist, where `free` returns a block to a pool and `alloc` reuses it, with a
proven invariant that the allocated and free regions stay **disjoint and tile the
managed region** — the reclaim invariant the critic said was missing. The KEY NEW
THING vs C7/C8: **memory is REUSED** — a freed address is handed back out — with a
proven partition invariant preserved across BOTH `alloc` (pop) and `free` (push).

## The model (fixed-size blocks + a singly-linked free list in memory)

A managed region is a fixed list `blocks` of fixed-size block addresses. A **free**
block stores, in its FIRST WORD, the address of the next free block (`0w` = NULL =
end of list). The free list is a singly-linked chain from a head pointer «head».
The two operations are the emitted panLang programs:

```
allocProg : ap := head ; head := *head          (pop the head block, return ap)
freeProg  : *fp := head ; head := fp             (push fp to the head of the list)
```

`alloc` only READS memory (the next pointer); `free` WRITES one word (the freed
block's first word). Both are byte-exact transcriptions of the run `.pnk`.

## THE ALLOCATOR INVARIANT — the reclaim invariant that was missing

```
allocInv blocks freeL allocL s ⇔
    ALL_DISTINCT blocks ∧ ¬MEM 0w blocks ∧
    PERM (freeL ++ allocL) blocks ∧                              (A) THE PARTITION
    linked s.memory freeL ∧                                      (B) valid chain
    FLOOKUP s.locals «head» = SOME (ValWord (chainHead freeL)) ∧ (C) head tracks list
    ∀x. MEM x blocks ⇒ x ∈ s.memaddrs                            (D) blocks available
```

- **(A) THE PARTITION — `PERM (freeL ++ allocL) blocks`.** The free blocks and the
  allocated blocks together are a permutation of the managed region: every block is
  in exactly one cell. This is a *single* fact that captures the whole tiling: with
  `ALL_DISTINCT blocks` it forces `ALL_DISTINCT (freeL ++ allocL)` (theorem
  `allocInv_distinct`), i.e. **disjoint** (no block is both free and allocated) and
  **no double-counting** — the blocks are exactly partitioned. This is the critic's
  "allocated and free regions stay disjoint and tile the arena", stated once.
- **(B) the free list is a VALID ACYCLIC CHAIN — `linked s.memory freeL`.**
  Inductively: each free block's first word holds the next block's address, the last
  holds `0w` (NULL). Acyclicity is free: `ALL_DISTINCT freeL` (from the partition)
  forbids a cycle. Note it constrains only the FREE blocks — an allocated block's
  content is the user's payload, exactly as a real allocator has it.
- **(C)/(D)** the head local tracks `chainHead freeL`; every managed block is in
  `s.memaddrs` so both operations can touch it.

## The headline theorems (verbatim, all `[oracles: DISK_THM] [axioms: ]`)

**`alloc` POPS a free block and PRESERVES the invariant** — a block moves from free
to allocated, memory unchanged (alloc only reads):
```
alloc_preserves_inv
|- allocInv blocks (a::rest) allocL s ∧
   (∃apv. FLOOKUP s.locals «ap» = SOME (ValWord apv)) ⇒
   ∃s'. evaluate (allocProg,s) = (NONE,s') ∧ s'.clock = s.clock ∧
        FLOOKUP s'.locals «ap»   = SOME (ValWord a) ∧          (* returns the popped block *)
        FLOOKUP s'.locals «head» = SOME (ValWord (chainHead rest)) ∧
        allocInv blocks rest (a::allocL) s'                     (* a moved free -> alloc *)
```

**`free` PUSHES a block and PRESERVES the invariant** — a block moves from
allocated to free, the freed block's first word now points to the old head, and the
OTHER free blocks' links survive (the write at `p` is disjoint from them, since `p`
is allocated hence not in `freeL`):
```
free_preserves_inv
|- allocInv blocks freeL allocL s ∧ FLOOKUP s.locals «fp» = SOME (ValWord p) ∧
   PERM allocL (p::allocL') ⇒
   ∃s'. evaluate (freeProg,s) = (NONE,s') ∧ s'.clock = s.clock ∧
        FLOOKUP s'.locals «head» = SOME (ValWord p) ∧
        (∀k. k ≠ «head» ⇒ FLOOKUP s'.locals k = FLOOKUP s.locals k) ∧
        allocInv blocks (p::freeL) allocL' s'                   (* p moved alloc -> free *)
```

**THE RECLAIM PROPERTY — free-then-alloc HANDS BACK the freed block (memory REUSE):**
```
freeThenAlloc_reuses
|- allocInv blocks freeL allocL s ∧ FLOOKUP s.locals «fp» = SOME (ValWord p) ∧
   (∃apv. FLOOKUP s.locals «ap» = SOME (ValWord apv)) ∧
   PERM allocL (p::allocL') ⇒
   ∃s'. evaluate (freeThenAlloc,s) = (NONE,s') ∧
        FLOOKUP s'.locals «ap»   = SOME (ValWord p) ∧           (* THE REUSE: freed p handed back *)
        FLOOKUP s'.locals «head» = SOME (ValWord (chainHead freeL)) ∧  (* head restored *)
        allocInv blocks freeL (p::allocL') s'
```
Free an allocated `p`, then `alloc`: the emitted `freeThenAlloc` returns the SAME
physical address `p` in «ap» — a freed address becomes usable again. This is the
reclaim step C7/C8 named as open: not just forward allocation, **the same block is
handed back out**, under a partition invariant proven preserved throughout.

## The NEW machinery (none of it in C0–C8)

- **`chainHead` / `linked`** — the freelist representation: `linked m addrs` says the
  memory function `m` links `addrs` into a singly-linked chain (each block's first
  word = next block, last = `0w`). This is the first datatype→memory relation that is
  a POINTER STRUCTURE (C7/C8's `wordsEncoded` was a flat array).
- **`linked_store_disjoint`** — the free-chain separation lemma: a store at an
  address DISJOINT from every chain block leaves the chain intact. This is what makes
  `free`'s single write (to the freed block's first word) preserve the OTHER free
  blocks' links. Proven by induction on the chain. (It is the freelist analogue of
  C7's `memRel_store_disjoint`, but over the linked structure being *extended*.)
- **`allocInv` + `allocInv_distinct`** — the partition invariant and the derivation
  that `PERM (…) blocks ∧ ALL_DISTINCT blocks` gives disjointness/tiling for free.
- **`PERM_pop`** — the partition-cell bookkeeping (`PERM ((a::rest)++xs) (rest++a::xs)`):
  moving a block between the free and allocated cells is a permutation, so the
  partition `PERM (…) blocks` is preserved by both pop and push. This is the crux
  that makes "disjoint + tile" a ONE-LINE consequence at each step rather than a
  bespoke set argument.
- **`eval_loadWord`** — the word LOAD (`Load One`, `*p`) semantics used by `alloc` to
  read the next pointer (C7/C8 only ever `Store`d words and `LoadByte`d input; the
  freelist is the first emission that LOADS a full word it earlier wrote).

The proofs are `panSem$evaluate`-level and small: `alloc` is memory-unchanged so the
chain and partition transfer directly; `free` writes one word, and the two facts
"the freed block now points to the old head" (chain grows by one) and "every other
free block's link survives" (`linked_store_disjoint`, disjoint because `p ∉ freeL`)
re-establish `linked`; `PERM_pop` re-establishes the partition. No loop induction —
these are straight-line operations — so the whole theory is ~6 s.

## Kernel 2 — the emitted `.pnk` compiles, runs, and REUSES a freed address

`pnk/freelist.pnk` builds a 4-block 16-byte arena, links it into a freelist
(`head -> b0 -> b1 -> b2 -> b3 -> NULL`), and runs the sequence
`alloc, alloc, free(alloc2), alloc` using the verified `allocProg`/`freeProg`
transcribed. `cake --pancake` compiled clean (exit 0, 226-line `.S`), linked
`cc -O2 … basis_ffi.c freelist_ffi.c`, and RAN:

```
alloc1 -> block0 (0x7d5931000210)
alloc2 -> block1 (0x7d5931000220)
free(alloc2)
alloc3 -> block1 (0x7d5931000220)
RECLAIM: alloc3 == alloc2  ->  FREED BLOCK REUSED (same address handed back out)
```

The reuse is byte-exact: alloc3's returned pointer (`0x…220`) is IDENTICAL to
alloc2's — the freed block address is handed back out by the next allocation,
matching `freeThenAlloc_reuses`'s `FLOOKUP s'.locals «ap» = SOME (ValWord p)`.
(`run/freelist_vectors.txt`, `pnk/freelist.pnk`, `pnk/freelist_ffi.c`, `pnk/freelist.S`.)

## The honest allocator verdict — updated

With a proven fixed-size LIFO freelist, **is basic reclaim now mechanical, or does
the invariant-preservation proof reveal a deeper gap?**

**Basic reclaim for FIXED-SIZE blocks is now MECHANICAL and proven — not research.**
The invariant-preservation proof did NOT reveal a deeper gap *for the fixed-size
LIFO case*: the partition invariant `PERM (freeL ++ allocL) blocks` is exactly the
right abstraction, and it is preserved by pop and push as a one-line permutation
(`PERM_pop`); the memory story is one separation lemma (`linked_store_disjoint`);
`free` writing into a block and `alloc` reading it are straight-line, needing no new
proof technique beyond C7's store lemmas plus a word LOAD. The allocator ledger now
reads:

- **Forward allocation** (C7 bump fixed + general-N; C8 data-driven collection) — proven.
- **RECLAIM: fixed-size LIFO freelist, `alloc`+`free` preserve a partition invariant,
  free-then-alloc reuses the freed address** (C9) — **proven (this probe).**

**What this leaves open toward a full verified allocator/GC (named precisely):**

1. **COALESCING.** Merging adjacent free blocks (and splitting on allocation) needs
   an ADDRESS-ORDERED invariant and arithmetic about block adjacency
   (`block_i + size = block_{i+1}`) — a genuinely richer invariant than the
   set-partition `PERM` used here, because it constrains *geometry*, not just
   membership. This is the first real step beyond C9 and is NOT here.
2. **VARIABLE-SIZE blocks.** Free lists per size class, or a single list with size
   headers and best/first-fit search, needs the size to be part of the block relation
   and a fit/split argument. The partition idea carries, but "blocks" is no longer a
   fixed list. NOT here.
3. **GC (reachability / relocation).** A tracing collector needs a reachability
   relation over the object graph, a mark/sweep or copying invariant, and — for a
   moving collector — updating interior pointers after relocation (the hardest part:
   the heap-shape relation must be preserved under a global address remap). NONE of
   this is modelled; it remains the deep open core.

Precise verdict: **the FIRST reclaim step — a fixed-size LIFO freelist that REUSES
freed memory, with a proven disjoint-and-tiling partition invariant preserved across
alloc and free — is now closed and kernel-checked. The critic's "verified
allocator/GC" gap is narrowed from "all of free/reclaim" to its remaining hard
pieces: COALESCING (adjacency geometry), VARIABLE-SIZE (fit/split), and GC
(reachability + relocation).** Memory REUSE — the thing C7/C8 said the bump
allocator fundamentally could not do — is now emitted and Link-A-proven.

## Standing boundaries (carried from C4–C8, none new, none an open proof item)

1. **FFI-oracle linkage.** `@report_freelist` is elided from the proof; the block
   slots are ASSUMED writable/readable (`∀x. MEM x blocks ⇒ x ∈ s.memaddrs`) and the
   initial freelist is ASSUMED linked (`linked s.memory freeL` in `allocInv`).
   Connecting these to the actual `ExtCall`/heap semantics is the one standing item,
   named since C4. In the run `.pnk` the initial chain is BUILT by emitted `Store`s
   (`st b0,b1; …`), independent evidence the `linked` hypothesis is realizable.
2. **Parser faithfulness.** `allocProg`/`freeProg` are the `.pnk` transcribed into
   the `panLang` AST by hand, not derived by `panPtreeConversion`. The compiled
   binary's byte-exact reuse on the run (Kernel 2) is independent evidence the
   transcription is faithful, but it is not a proof.
3. **Link B (`pan_to_target`).** Inherited from the CakeML tree
   (`pan_to_target_compile_semantics`, `check_thm`'d) — the cited half, not re-done.

## Files (under `docs/engine/probes/compiler/`)

- `hol-c9/arenaFreelistLinkAScript.sml` — the theory: `chainHead`/`linked`/
  `linked_store_disjoint`; `allocInv`/`allocInv_distinct`; `PERM_pop`; `allocProg`/
  `freeProg`/`freeThenAlloc`; `eval_loadWord`/`eval_assignVar`/`eval_assignLoad`;
  `alloc_preserves_inv`; `free_preserves_inv`; `freeThenAlloc_reuses`. Opens/reuses
  C7 (`eval_storeVar`), C3 (`Seq_NONE`), plus `sortingTheory` (PERM).
- `hol-c9/Holmakefile`, `hol-c9/verify_out.txt` — statements + `[oracles]`/`[axioms]`
  tags + the `axioms = 0` footprint.
- `pnk/freelist.pnk`, `pnk/freelist_ffi.c`, `pnk/freelist.S` — the emitted reclaiming
  Pancake, its FFI driver, and the `cake` output.
- `run/freelist_vectors.txt` — the two-kernel run (the reuse observation).

## Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`, in a work
dir holding the C2–C8 scripts + `arenaFreelistLinkAScript.sml` + `Holmakefile`:
```
export CAKEMLDIR=$HOME/src/cakeml && export PATH=$HOME/src/HOL/bin:$PATH
Holmake arenaFreelistLinkATheory.uo      # builds C2..C8 then C9, green (~6 s C9)
```
Kernel 2: `cake --pancake < pnk/freelist.pnk > freelist.S ;
cc -O2 freelist.S basis_ffi.c pnk/freelist_ffi.c -o freelist -lm ; ./freelist`
→ `alloc3 == alloc2 -> FREED BLOCK REUSED`.

## Bottom line for Phase C

C7 built a data structure in memory (bump, fixed + general-N); C8 did the whole
data-driven collector; both only ever ADVANCED the pointer. C9 is the first emission
that **REUSES** memory: a fixed-size LIFO freelist where `free` returns a block and
`alloc` hands it back out, with a proven PARTITION invariant (free ⊎ alloc = blocks,
disjoint and tiling) preserved across both operations and a kernel-checked reclaim
theorem that free-then-alloc returns the SAME physical block — Link-A-proven against
real `panSem`, compiled and observed byte-exact, clean kernel footprint (0 axioms, 0
cheats). The C7/C8-named "free/reclaim" gap is OPENED at its first honest step; what
remains is precisely COALESCING, VARIABLE-SIZE, and GC.
