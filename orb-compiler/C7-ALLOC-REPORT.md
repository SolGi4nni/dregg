# C7 — the FIRST allocating, memory-BUILDING emission: a bump-allocated span array with a proven memory-layout relation, Link-A-proven both FIXED-count and GENERAL-N

**Date:** 2026-07-04 · **Machine:** hbox (i9-12900) HOL4/CakeML; drorb (Lean) model kernel.
**Status: DONE, and stronger than the goal asked for.** One HOL4 theory
(`hol-c7/arenaAllocLinkAScript.sml`), 20 kernel-checked theorems, **every one
`[oracles: DISK_THM] [axioms: ]`, `axioms "arenaAllocLinkA" = 0`, zero
`cheat`/`new_axiom`/`mk_thm`/oracle in source.** Clean from-scratch rebuild
`arenaAllocLinkATheory [1/1] OK` in ~6 s on the C2/C3/C5/C6 chain. The emitted
Pancake compiles with `cake`, links, and RUNS — the bytes it writes into memory
match the Lean parser and the Lean fill spec on every vector.

## The gap the critic named, and what C7 closes

Everything C0–C6 emitted was a first-order byte-SCAN over a flat immutable
buffer: it READ bytes (`LoadByte`) and left its answer in **locals** (or, in C4,
a single result word). Nothing built a data structure in memory. The adversarial
critic graded exactly that as the load-bearing RESEARCH gap: *"lists → a verified
allocator/GC."*

C7 takes the first real bite — and lands two of them:

1. **`writeSpans` (FIXED count, the REAL parser output).** `parseRequestLine`'s
   result is a STRUCTURE: three spans, each an `(offset,length)` pair — a
   `List Span`. C7 emits a bump-pointer program that ALLOCATES a region and
   WRITES those three records into Pancake memory, and proves against real
   `panSem$evaluate` that the flat memory it produces ENCODES exactly the Lean
   `parseReqLine` output list.

2. **`fillLoop` (GENERAL N, the allocation MECHANISM).** A bump-allocating LOOP
   that writes a **data-dependent** number `N` of records into the arena, the
   bump pointer advancing by the element size each iteration, and proves — by
   loop-invariant induction over the clocked `While`, for ALL `N` — that the
   arena ends up ENCODING the length-`N` list the spec returns.

Plus the **separation lemma** — the verified memory story that makes an allocator
which writes-while-it-reads sound.

## The NEW machinery (none of it existed in C0–C6)

### The memory-layout relations — the datatype→flat-memory encoding the critic said did not exist

```
spansEncoded spans outB s ⇔
  ∀k. k < LENGTH spans ⇒
      s.memory (outB + n2w (16*k))     = Word (n2w (FST spans[k])) ∧
      s.memory (outB + n2w (16*k + 8)) = Word (n2w (SND spans[k]))

wordsEncoded xs outB s ⇔
  ∀k. k < LENGTH xs ⇒ s.memory (outB + n2w (8*k)) = Word (n2w xs[k])
```

A Lean `List (num × num)` (or `List num`) is **represented** at flat base `outB`
iff record `k` is laid down at `outB + recordSize*k`. panSem memory is
`word → word_lab`; a full-word `Store` lands a `Word w` at its (word-aligned)
address, so the relation reads the raw memory function — the same shape C4 read
its single result word back through, now generalised to an addressed ARRAY.

### Headline theorems (verbatim, all `[oracles: DISK_THM] [axioms: ]`)

**Fixed-count Link A — the emitted allocating writer builds the Lean parser's structure:**
```
writeSpans_refines_parseReqLine
|- parseReqLine off line = SOME ((mOff,mLen),(tOff,tLen),(vOff,vLen)) ∧
   FLOOKUP s.locals «out» = SOME (ValWord outB) ∧ <the six span fields in locals> ∧
   (∃bpv. FLOOKUP s.locals «bp» = SOME (ValWord bpv)) ∧ arena6 outB s ⇒
   ∃s'. evaluate (writeSpans, s) = (NONE, s') ∧
        spansEncoded (spanListOf (parseReqLine off line)) outB s'
```
i.e. whenever the Lean `parseRequestLine` returns SOME spans, the emitted
`writeSpans` runs to completion (`NONE` — no Error, no TimeOut) and the arena
memory ENCODES *exactly the `List Span` the Lean parser returns*. Its engine
`writeSpans_encodes` also proves the bump pointer «bp» is advanced to
`out + 48` (= recordSize × count) — the allocation consumed 48 bytes.

**General-N Link A — the bump-allocating loop builds a length-N structure, for ALL N:**
```
fillLoop_refines
|- FLOOKUP s.locals «k»  = SOME (ValWord 0w) ∧
   FLOOKUP s.locals «n»  = SOME (ValWord (n2w N)) ∧
   FLOOKUP s.locals «bp» = SOME (ValWord outB) ∧
   N < 2**63 ∧ 8*N < dimword(:64) ∧
   (∀j. j < N ⇒ outB + n2w (8*j) ∈ s.memaddrs) ∧ N ≤ s.clock ⇒
   ∃s'. evaluate (fillLoop, s) = (NONE, s') ∧
        wordsEncoded (GENLIST (λi. i) N) outB s'
```
From a fresh loop state (`k=0`, bump pointer at `out`, arena available for all N
slots, nothing written), with enough clock, the emitted `while (k<n) { st bp,k;
bp+=8; k++; }` builds, in the arena, EXACTLY the length-N list `GENLIST (λi.i) N`
— a **data-dependent count** of records at an advancing bump pointer, with the
layout relation proven **by induction**. This is the general allocation
mechanism the critic asked whether was mechanical.

**The separation lemma — the verified memory story:**
```
memRel_store_disjoint
|- memRel input bs s ∧ (∀j. j < LENGTH input ⇒ a ≠ byte_align (bs + n2w j)) ⇒
   memRel input bs (s with memory := (a =+ Word v) s.memory)
```
An output-arena write (a full-word `Store` at `a`) DISJOINT from the input buffer
preserves the input byte-relation `memRel` (C3, reused). This is what makes an
allocator that writes into a bump arena WHILE the scan still reads the input
sound — the seam an input-driven collect loop rides.

### The loop's proof structure (reuses C5, adds the write)

`fillLoop_run` is the loop-invariant induction over the clocked `While`, the
**same skeleton as C5's `scanLoop_scan_bounded`**, reused. The invariant `fillInv`
carries the bump pointer (`«bp» = outB + n2w(8*k)`), the count/length scalars, the
arena availability, and — the genuinely new part — the growable layout relation
`wordsEncoded (GENLIST (λi.i) k) outB s` (records `0..k-1` already written). The
step lemmas:
- **`fillBody_eval`** — the whole loop body evaluated in one shot over a symbolic
  state (`Store` the element, advance `bp`, increment `k`), reusing C5's
  `eval_storeVar` shape.
- **`wordsEncoded_extend`** — the LAYOUT-PRESERVATION lemma: writing element `k`
  at the k-th bump slot extends the encoded list from `k` to `k+1` records; the
  earlier records survive because the new write is at a distinct (higher) bump
  address (bump distinctness `slot8_neq`, pure `n2w` injectivity), and the new
  record is written. This is the crux — the layout relation is **preserved and
  extended** by each bump-write.
- **`fillBody_step`** glues them and re-establishes `fillInv` at `k+1`.

## Kernel 2 — the emitted `.pnk` compiles, runs, and matches the Lean spec

`pnk/arenawrite.pnk` (parse the request line, then (1) `writeSpans` the 3 span
records into a bump arena, and (2) `fillLoop` a general-N arena `[0..i1-1]` with
`N = i1` **data-dependent** = the method length). `cake --pancake` compiled clean
(exit 0, 270-line `.S`), linked `cc -O2 … basis_ffi.c arenawrite_ffi.c`, and RUN;
the FFI reporter dumps the raw bump-region bytes back:

```
LINE="GET / HTTP/1.1"            -> spans: method=(0,3) target=(4,1)  version=(6,8)    ;  fill[N=3]: 0 1 2
LINE="POST /api/v1/users HTTP/1.1"-> spans: method=(0,4) target=(5,13) version=(19,8)  ;  fill[N=4]: 0 1 2 3
LINE="GET /index.html HTTP/1.0"  -> spans: method=(0,3) target=(4,11) version=(16,8)   ;  fill[N=3]: 0 1 2
LINE="DELETE /a/b/c HTTP/2"      -> spans: method=(0,6) target=(7,6)  version=(14,6)   ;  fill[N=6]: 0 1 2 3 4 5
```

The `spans:` line is the `writeSpans` arena read back — three `(offset,length)`
records that agree with the real Lean `parseRequestLine` (identical to C6's
verified vectors). The `fill[N=k]:` line is the general-N loop's arena read back —
`[0,1,…,N-1] = GENLIST (λi.i) N`, with `N` the data-dependent method length —
matching `fillLoop_refines`'s spec. **Both structures are BUILT IN MEMORY by the
emitted program and observed, byte for byte, to match the proofs.**
(`run/arenawrite_vectors.txt`, `pnk/arenawrite.pnk`, `pnk/arenawrite_ffi.c`.)

## Is a verified allocator still "research"? — the honest verdict

**Bump allocation with a proven memory-layout relation is now MECHANICAL, and
proven — not research.** Both directions are closed, kernel-checked, against real
`panSem`:
- **the real parser's structured output at a FIXED count** (`writeSpans` ⇒ the
  Lean `List Span`), and
- **a data-dependent GENERAL-N count laid down by a loop** (`fillLoop` ⇒
  `GENLIST (λi.i) N`, for all N, layout relation proven by induction).

So the critic's "lists → a verified allocator" is answered for the bump case: the
allocation is pointer arithmetic (`bp += recordSize`), the "build" is a full-word
`Store`, and the datatype→flat-memory ENCODING now EXISTS as a proven relation
(`spansEncoded`/`wordsEncoded`) that a loop **preserves and extends**
(`wordsEncoded_extend`). None of it needed a new proof technique beyond C5's loop
induction plus the store/layout lemmas.

**What a verified GENERAL / RECLAIMING allocator still needs (genuinely open):**
- **`fillLoop` writes SCHEMATIC content** (record `k` = `k`). It proves the
  general bump-allocate-and-encode LOOP mechanism, not a data-driven payload. The
  fully-real general-N parser collect loop (`collectSp`: scan the input and PUSH
  each delimiter offset — variable count from the DATA, not a counter) additionally
  READS the input every iteration. Its soundness is exactly the separation lemma
  `memRel_store_disjoint` (proven here) threaded through the combined scan-read +
  bump-push induction — a mechanical composition of C5's `scanLoop` read with C7's
  `fillBody` write, not yet assembled. This is the named residual for the *real*
  variable-length collector.
- **No free / reclaim.** The bump pointer only advances. A verified allocator with
  `free`, a freelist, coalescing, or fragmentation reasoning is NOT modelled and
  IS still open research.
- **No GC.** Reachability, a moving/compacting collector, updating interior
  pointers after relocation — none of that is here, and all of it remains open.

So the precise verdict: **allocation is now mechanical-for-bump (proven, fixed
AND general-N); reclaiming/reusing/collecting allocation is still open research.**
The critic's "verified allocator/GC" gap is narrowed to exactly its hard core —
memory REUSE and reachability — with the whole *forward* (allocate + write +
encode) half now closed and kernel-checked.

## Standing boundaries (carried from C4–C6, none new, none an open proof item)

1. **FFI-oracle linkage.** `@load_line`/`@report_arena` are elided; the input is
   ASSUMED in the buffer (`memRel`) and the arena slots ASSUMED in `memaddrs`
   (`arena6` / `fillInv`'s `∀j…∈ memaddrs`). Connecting these to the actual
   `ExtCall` semantics (`read_bytearray`/`write_bytearray`/endianness) is the one
   standing item, named since C4.
2. **Parser faithfulness.** `writeSpans`/`fillLoop`/`fillBody` are the `.pnk`
   transcribed into the `panLang` AST by hand, not derived by running
   `panPtreeConversion` on `arenawrite.pnk`. The compiled binary's byte-exact
   agreement on the vectors (Kernel 2) is independent evidence the transcription
   is faithful, but it is not a proof.
3. **Link B (`pan_to_target`).** Inherited from the CakeML tree
   (`pan_to_target_compile_semantics`, `check_thm`'d) — the cited half, not re-done.

## Mechanisation note (what the general-N proof cost)

The general-N loop's `fillBody_step` is a genuine HOL4 rewriter minefield, and two
specific pathologies were paid for and are recorded so the next component avoids
them:
- **`simp` over word arithmetic loops.** `simp [GSYM word_add_n2w]` cycles against
  the built-in forward `word_add_n2w` (`n2w(a+b) ⇄ n2w a + n2w b`), and
  `once_rewrite [WORD_ADD_COMM]` / `simp [AC …]` over `outB + n2w(8*k)` terms
  churn to tens of GB / never terminate. Fix: normalise addresses with **explicit
  `REWRITE_TAC`/`metis_tac [WORD_ADD_COMM]`**, never a word-arith `simp`.
- **`irule` of a lemma whose hypotheses introduce an existential.** `irule
  fillInv_words` leaves `∃N. fillInv N …` (N not in the conclusion) — needs an
  explicit `qexists_tac`; and `irule wordsEncoded_extend` yields `A ∧ (∃s. B ∧ C)`
  with the existential NESTED inside the conjunction, so `conj_tac` must peel `A`
  *before* `qexists_tac`. Both fail silently under interactive `e`, which is why
  the whole-body lemma (`fillBody_eval`) and the isolated preservation lemma
  (`wordsEncoded_extend`) are proved over SYMBOLIC states and merely instantiated
  — keeping every simp small and the quantified layout relation out of the
  induction's general context (the C6 blowup discipline).

## Files (under `docs/engine/probes/compiler/`)

- `hol-c7/arenaAllocLinkAScript.sml` — the theory: `spansEncoded`/`wordsEncoded`
  layout relations; `writeSpans` + `writeSpans_encodes` + `writeSpans_refines_parseReqLine`;
  `memRel_store_disjoint`; `fillLoop` + `fillBody_eval` + `wordsEncoded_extend` +
  `fillBody_step` + `fillLoop_run` + `fillLoop_refines`. Opens/reuses C3 (`memRel`,
  `Seq_NONE`), C5 (`scanLoop` skeleton lemmas via `signed_lt_n2w64`), C6
  (`parseReqLine`).
- `hol-c7/Holmakefile`, `hol-c7/verify_out.txt` — statements + `[oracles]`/`[axioms]`
  tags + the `axioms = 0` footprint.
- `pnk/arenawrite.pnk`, `pnk/arenawrite_ffi.c`, `pnk/arenawrite.S` — the emitted
  allocating Pancake, its FFI driver, and the `cake` output.
- `run/arenawrite_vectors.txt` — the two-kernel vector table.

## Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`, in a work
dir holding the C2/C3/C5/C6 scripts + `arenaAllocLinkAScript.sml` + `Holmakefile`:
```
export CAKEMLDIR=$HOME/src/cakeml && export PATH=$HOME/src/HOL/bin:$PATH
Holmake arenaAllocLinkATheory.uo      # builds C2,C3,C5,C6 then C7, green (~6 s C7)
```
Kernel 2: `cake --pancake < pnk/arenawrite.pnk > arenawrite.S ;
cc -O2 arenawrite.S basis_ffi.c pnk/arenawrite_ffi.c -o arenawrite -lm ;
LINE="GET / HTTP/1.1" ./arenawrite`.

## Bottom line for Phase C

C5 paid the loop-induction long pole on a scan; C6 composed two scans. C7 is the
first emission that BUILDS A DATA STRUCTURE IN MEMORY: a bump-allocated array of
records with a proven memory-LAYOUT relation, Link-A-proven against real `panSem`
both at a FIXED count (the real parser's `List Span`) and at a GENERAL, data-
dependent N (a loop, layout preserved by induction), compiled and observed
byte-exact against the Lean spec, with a clean kernel footprint (0 axioms, 0
cheats). The critic's "verified allocator" gap is now closed for the *forward*
(allocate + write + encode) half — mechanical for bump — with the residual sharply
named: an input-driven variable-length collector (mechanical composition of the
proven scan-read + bump-write under the proven separation lemma), and — the true
open research — memory REUSE (free/reclaim) and GC (reachability/relocation).
