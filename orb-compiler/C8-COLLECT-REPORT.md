# C8 — the REAL VARIABLE-LENGTH COLLECTOR: a single scan-push loop that READS the input and PUSHES a data-dependent number of data-derived records to a bump arena, Link-A-proven against real panSem

**Date:** 2026-07-05 · **Machine:** hbox (i9-12900) HOL4/CakeML; drorb (Lean) model kernel.
**Status: DONE — the C7-named residual is CLOSED.** One HOL4 theory
(`hol-c8/arenaCollectLinkAScript.sml`), 8 kernel-checked theorems, **every one
`[oracles: DISK_THM] [axioms: ]`, `axioms "arenaCollectLinkA" = 0`, zero
`cheat`/`new_axiom`/`mk_thm`/oracle in source.** Clean from-scratch rebuild
`arenaCollectLinkATheory [1/1] OK` in ~6 s on the C2/C3/C5/C6/C7 chain. The emitted
Pancake compiles with `cake` (exit 0), links, and RUNS — the offset list it BUILDS
IN MEMORY matches the Lean/HOL `collectSp` spec byte-for-byte on every vector.

## The residual C7 named, and what C8 closes

C7 landed two allocation bites: `writeSpans` (FIXED count, the real parser's three
spans) and `fillLoop` (GENERAL N, but **schematic content** — record `k = k`, a
pure counter that never reads the input). C7 named the load-bearing residual
verbatim:

> *"The fully-real general-N parser collect loop (`collectSp`: scan the input and
> PUSH each delimiter offset — variable count from the DATA, not a counter)
> additionally READS the input every iteration. Its soundness is exactly the
> separation lemma `memRel_store_disjoint` (proven here) threaded through the
> combined scan-read + bump-push induction — a mechanical composition of C5's
> `scanLoop` read with C7's `fillBody` write, not yet assembled."*

**C8 assembles exactly that.** The emitted loop is
```
i = 0; bp = out;
while (i < len) {
  b = ld8 (base + i);                       // scan-READ the input byte
  if (b == 32) { st bp, i;  bp = bp + 8; }  // PUSH the delimiter offset i
  i = i + 1;
}
```
and its arena ends ENCODING exactly `collectSp input` = the list of offsets of the
delimiter bytes, **in order** — a **data-dependent COUNT** (the number of
delimiters) and **data-derived CONTENT** (the offsets, determined entirely by the
input bytes). This is the first emission where **both** the input-read relation and
the arena-layout relation are live at once and threaded through **one** induction.

## The Lean/HOL spec (the collector, not a counter)

```
collectFrom off []      = []
collectFrom off (b::bs) = if b = 32 then off :: collectFrom (off+1) bs
                                    else collectFrom (off+1) bs
collectSp input = collectFrom 0 input
```
`collectSp input` is a `List num` whose LENGTH is data-dependent (the number of
delimiters) and whose CONTENT is data-derived (the offsets where the input holds a
delimiter). Nothing schematic: strike out a delimiter and the list gets a member;
move it and the member moves.

## The headline theorem (verbatim, `[oracles: DISK_THM] [axioms: ]`)

```
collectLoop_refines_collectSp
|- FLOOKUP s.locals «i»  = SOME (ValWord 0w) /\
   FLOOKUP s.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «bp» = SOME (ValWord outB) /\
   (∃bb. FLOOKUP s.locals «b» = SOME (ValWord bb)) /\ memRel input bs s /\
   LENGTH input < 2**63 /\ 8*LENGTH input < dimword(:64) /\
   EVERY (λx. x < 256) input /\
   (∀j. j < LENGTH input ⇒ outB + n2w (8*j) ∈ s.memaddrs) /\
   (∀m j. m < LENGTH input ∧ j < LENGTH input ⇒
            outB + n2w (8*m) ≠ byte_align (bs + n2w j)) /\       <- the SEPARATION precond
   LENGTH input ≤ s.clock ⇒
   ∃s'. evaluate (collectLoop, s) = (NONE, s') /\
        wordsEncoded (collectSp input) outB s' /\                <- arena ENCODES collectSp
        FLOOKUP s'.locals «bp» =
          SOME (ValWord (outB + n2w (8 * LENGTH (collectSp input))))   <- alloc consumed
```
From a fresh (`i=0`, `bp=out`) state with enough clock and the separation
precondition, the emitted `While` TERMINATES (`NONE` — no Error, no TimeOut) and
the arena memory ENCODES *exactly the `List num` the Lean spec returns*, with the
bump pointer advanced to `out + 8*LENGTH(collectSp input)` (the allocation
consumed). Proven against real `panSem$evaluate`.

## The one induction that threads BOTH relations (the genuinely new thing)

`collectBody_step` is the crux — one iteration of the body, over real
`panSem$evaluate`, re-establishing the invariant `colInv` at `i+1`:

```
colInv input bs outB i s ⇔
   <the emitted scalars «i» «len» «base» and a byte slot «b»> /\
   FLOOKUP s.locals «bp» = SOME (ValWord (outB + n2w (8 * LENGTH (collectFrom 0 (TAKE i input))))) /\
   memRel input bs s /\                                          (A) the INPUT-READ relation
   <bounds, arena availability, the SEPARATION precondition> /\
   wordsEncoded (collectFrom 0 (TAKE i input)) outB s            (B) the LAYOUT relation
```

The body reads the `i`-th byte (`memRel` + `w2w_byte`) and BRANCHES:

- **delimiter HIT** (`input[i] = 32`): `Store` the offset `i` at the bump slot
  `out + 8*k` (`k = LENGTH(collectFrom 0 (TAKE i input))`), advance `bp`, `i++`.
  Both relations are re-established at `i+1`:
  - **(A) memRel is PRESERVED** — the push is a full-word `Store` at an address
    byte-DISJOINT from the input buffer (discharged from the separation precondition
    via C7's `memRel_store_disjoint`). This is the seam the report said the
    collector rides, now actually ridden.
  - **(B) the layout relation is EXTENDED by one record** — `wordsEncoded_snoc`
    (the data-driven generalisation of C7's schematic `wordsEncoded_extend`) takes
    the encoded list from `k` to `k+1`: earlier records survive (distinct, lower
    slots, `slot8_neq`), the new offset `i` is written. Matched to the spec by
    `collect_step_hit`: `collectFrom 0 (TAKE (i+1) input) = collectFrom 0 (TAKE i input) ++ [i]`.

- **delimiter MISS** (`input[i] ≠ 32`): the `If` takes the `Skip` arm, no push,
  just `i++`. `collect_step_miss` gives `collectFrom 0 (TAKE (i+1) input) =
  collectFrom 0 (TAKE i input)`; both relations carry unchanged.

`collectLoop_run` is the loop-invariant induction over the clocked `While` (C5's
`scanLoop_scan_bounded` / C7's `fillLoop_run` skeleton), threading the clock down
one per iteration; `collectLoop_refines_collectSp` instantiates it from the fresh
state (`TAKE 0 input = []`, `collectFrom 0 [] = []`, `bp = out`).

**What is genuinely new over C5+C7:** C5's `scanLoop` READ the input and left its
answer in a local; C7's `fillLoop` WROTE the arena but its content was a schematic
counter. C8 is the first loop that does BOTH at once — reads the input to decide,
writes input-derived content to the arena — with the read-relation (A) and the
layout-relation (B) simultaneously live and preserved through the *same*
scan-push induction. That composition is the thing C7 named as "not yet assembled".

## Kernel 2 — the emitted `.pnk` compiles, runs, and matches the spec byte-exact

`pnk/collect.pnk` is a byte-exact transcription of the verified `collectBody` AST
(locals «base» «i» «len» «bp» «b»). `cake --pancake` compiled clean (exit 0,
242-line `.S`), linked `cc -O2 collect.S basis_ffi.c collect_ffi.c`, and RAN; the
FFI reporter dumps (1) the arena the loop built, read back, and (2) `collectSp`
recomputed directly from `$LINE` — the two agree on every vector:

```
LINE="GET / HTTP/1.1"               -> collect[n=2]: 3 5        spec: 3 5
LINE="POST /api/v1/users HTTP/1.1"  -> collect[n=2]: 4 18       spec: 4 18
LINE="GET /index.html HTTP/1.0"     -> collect[n=2]: 3 15       spec: 3 15
LINE="DELETE /a/b/c HTTP/2"         -> collect[n=2]: 6 13       spec: 6 13
LINE="a b c d e"                    -> collect[n=4]: 1 3 5 7     spec: 1 3 5 7
LINE="nospaces"                     -> collect[n=0]:            spec:
LINE="  leading"                    -> collect[n=2]: 0 1        spec: 0 1
LINE="trailing  "                   -> collect[n=2]: 8 9        spec: 8 9
```
The COUNT is data-dependent (`n` ranges 0..4 across the vectors); the CONTENTS are
read from the input (the actual delimiter offsets). **The list is BUILT IN MEMORY by
the emitted program and observed, byte for byte, to match `collectSp`.**
(`run/collect_vectors.txt`, `pnk/collect.pnk`, `pnk/collect_ffi.c`, `pnk/collect.S`.)

## The honest allocator verdict — updated

C7 closed the *forward* allocation half for **schematic** content (bump + write +
encode, fixed and general-N). C8 removes the "schematic" caveat:

**Variable-length allocating COLLECTION is now MECHANICAL and proven — not
research.** The interleaved scan-read + bump-push did NOT reveal a further gap: it
is exactly the mechanical composition C7 predicted. The only genuinely new lemma
needed was `wordsEncoded_snoc` — pushing an *arbitrary data value* (not a counter)
extends the layout relation — plus routing the already-proven `memRel_store_disjoint`
through the loop from a **separation precondition** (arena byte-disjoint from
input). No new proof *technique* beyond C5's loop induction and C7's store/layout
lemmas; the scan-read and the bump-push simply co-inhabit one invariant.

So, with the real collector proven, the allocator ledger now reads:
- **FIXED-count structured allocation** (C7 `writeSpans` ⇒ the real parser's `List Span`) — proven.
- **GENERAL-N schematic allocation** (C7 `fillLoop` ⇒ `GENLIST (λi.i) N`) — proven.
- **GENERAL-N, DATA-DRIVEN COLLECTION** (C8 `collectLoop` ⇒ `collectSp input`, count
  from data, content read from input, memRel + layout threaded through one
  scan-push induction) — **proven (this probe).**

**What remains genuinely open (unchanged, and it is the hard core):**
- **No free / reclaim.** The bump pointer only advances. A verified allocator with
  `free`, a freelist, coalescing, or fragmentation reasoning is NOT modelled and is
  still open research.
- **No GC.** Reachability, a moving/compacting collector, updating interior
  pointers after relocation — none of it is here, and all of it remains open.

Precise verdict: **the entire FORWARD allocating story — allocate + write + encode,
fixed, general-N, AND data-driven variable-length collection — is now closed and
kernel-checked. The critic's "verified allocator/GC" gap is narrowed to exactly its
irreducible core: memory REUSE (free/reclaim) and reachability (GC).**

## Standing boundaries (carried from C4–C7, none new, none an open proof item)

1. **FFI-oracle linkage.** `@load_line`/`@report_collect` are elided; the input is
   ASSUMED in the buffer (`memRel`), the arena slots ASSUMED writable
   (`∀j…∈ memaddrs`), and the arena ASSUMED byte-disjoint from the input (the
   separation precondition `∀m j… ≠ byte_align …`). Connecting these to the actual
   `ExtCall` semantics (`read_bytearray`/`write_bytearray`/endianness) is the one
   standing item, named since C4. The separation precondition is a genuine, honestly
   stated hypothesis — the collector is sound *because* the arena is disjoint from
   the input, and that disjointness is the caller's obligation, discharged in the
   real allocator by putting the arena in a distinct region.
2. **Parser faithfulness.** `collectLoop`/`collectBody`/`collectGuard` are the
   `.pnk` transcribed into the `panLang` AST by hand (locals «base» «i» «len» «bp»
   «b»), not derived by running `panPtreeConversion` on `collect.pnk`. The compiled
   binary's byte-exact agreement on the vectors (Kernel 2) is independent evidence
   the transcription is faithful, but it is not a proof.
3. **Link B (`pan_to_target`).** Inherited from the CakeML tree
   (`pan_to_target_compile_semantics`, `check_thm`'d) — the cited half, not re-done.

## Files (under `docs/engine/probes/compiler/`)

- `hol-c8/arenaCollectLinkAScript.sml` — the theory: `collectFrom`/`collectSp` spec;
  `collectFrom_append`/`collectFrom_length_le`/`collect_step_hit`/`collect_step_miss`
  list lemmas; `wordsEncoded_snoc` (data-driven layout extension); `collectGuard`/
  `collectBody`/`collectLoop` + `colInv` + `collectBody_step` + `collectLoop_unfold`
  + `collectLoop_run` + `collectLoop_refines_collectSp`. Opens/reuses C3 (`memRel`,
  `w2w_byte`, `Seq_NONE`, `fix_clock_id`), C2 (`signed_lt_n2w64`), C5 (`TAKE_SUC_SNOC`),
  C7 (`wordsEncoded`, `slot8_neq`, `eval_storeVar`, `eval_assign_addC`,
  `memRel_store_disjoint`).
- `hol-c8/Holmakefile`, `hol-c8/verify_out.txt` — statements + `[oracles]`/`[axioms]`
  tags + the `axioms = 0` footprint.
- `pnk/collect.pnk`, `pnk/collect_ffi.c`, `pnk/collect.S` — the emitted collecting
  Pancake, its FFI driver, and the `cake` output.
- `run/collect_vectors.txt` — the two-kernel vector table.

## Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`, in a work
dir holding the C2/C3/C5/C6/C7 scripts + `arenaCollectLinkAScript.sml` + `Holmakefile`:
```
export CAKEMLDIR=$HOME/src/cakeml && export PATH=$HOME/src/HOL/bin:$PATH
Holmake arenaCollectLinkATheory.uo      # builds C2..C7 then C8, green (~6 s C8)
```
Kernel 2: `cake --pancake < pnk/collect.pnk > collect.S ;
cc -O2 collect.S basis_ffi.c pnk/collect_ffi.c -o collect -lm ;
LINE="GET / HTTP/1.1" ./collect`   ->   `collect[n=2]: 3 5   spec: 3 5`.

## Bottom line for Phase C

C5 paid the loop-induction long pole on a scan; C6 composed two scans; C7 built a
data structure in memory (fixed and general-N, schematic content). C8 is the first
emission that does the WHOLE collector: SCAN the input, PUSH a data-dependent number
of records whose CONTENT is read from the data, into a bump arena, with the input-
read relation and the arena-layout relation threaded through ONE scan-push
induction — Link-A-proven against real `panSem` (`collectLoop_refines_collectSp`),
compiled and observed byte-exact against the Lean `collectSp` spec, clean kernel
footprint (0 axioms, 0 cheats). The C7-named "variable-length collector" residual is
CLOSED. The verified-allocator gap is now exactly its hard core: **free/reclaim and
GC**.
