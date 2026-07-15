# COMPILER-SYMPATHY-BACKLOG — the LATER, upstream-in-the-loop performance track

Status: **BACKLOG. Not now.** This document captures the mechanical-sympathy
work that would make the emitted serve code *faster*, and does not do any of it.
Every item here is a change to the **verified compiler** (CakeML) or its source
language (Pancake) — the trusted computing base of the whole translator chain.
That is exactly why none of it happens on the current arc: touching the TCB is a
different kind of work from extending our Lean-side translator, and it can only
be done *upstream, in coordination with CakeML*, carrying a machine-checked
correctness proof for every change and never forking the compiler.

The current arc's job is to close the **correctness** chain: one proven
translator that swallows the real serve and emits code paired with a refinement
certificate (see `TRANSLATOR-ARC.md`). Correctness first; sympathy later. The
measured gap this track would close is the well-known scalar-codegen overhead of
the verified backend (the emitted code runs at roughly native-C speed within a
small constant factor); closing it is a quality-of-codegen exercise, not a
capability the serve needs to be correct.

---

## The three non-negotiables that make every item here "upstream-coordinated"

1. **It edits the verified TCB.** Each item changes either the Pancake source
   language (`pancake/panLangScript.sml`, `panSemScript.sml`) or a compiler
   backend pass (`compiler/backend/…`). Our translator's faithfulness rests on
   the Lean model of Pancake semantics (`Pancake/Sem.lean`) matching the real
   `panSem`, and on the CakeML compiler-correctness theorem. Any change to the
   language or a pass re-opens both.

2. **It must carry the Link-B / faithfulness proof.** Our chain has a single
   named faithfulness assumption (the A1 audit surface: `Pancake/Sem.lean`'s
   model = `panSem` on the modelled subset). Adding an operator, a layout, or an
   ABI shape means re-establishing that the Lean model still mirrors the extended
   `panSem`, plus the CakeML side must extend `compile_correct` across the new
   construct through every intermediate language. A feature that runs but breaks
   the proof is not admissible.

3. **It must not fork CakeML.** The value of the verified backend is that it is
   *the* upstream, community-reviewed, continuously-proved compiler. A private
   fork loses that and rots. Every item here is framed as an upstream PR against
   CakeML with its proof obligations discharged, not a local patch. Landing takes
   upstream review latency; that is the cost of staying on the verified rail.

The honest consequence: this whole track is **slower to land** than Lean-side
work, gated on upstream, and correctly scheduled **after** the correctness arc.

---

## Item 1 — enable `Div` and `Mod` in the Pancake op set

**The current workaround.** The serve renders decimal numbers (status codes,
`Content-Length`) with `natToDec`, proved as a bounded divide-by-10 digit loop:
`Pancake/SerializeCompile.lean` §1 defines `decAux fuel n acc = if n < 10 then …
else decAux fuel (n / 10) (digitByte (n % 10) :: acc)`, and proves the round trip
`natToDec_readback : readFrom 0 (natToDec n) = n` (axiom-clean, 0 `sorry`, no
`native_decide`). That spec uses Lean's `n / 10` and `n % 10`. But the machine
subset the translator emits into **has no divide or modulo instruction**. At
`ed31510b3` the Pancake op datatype is literally:

```
  (* pancake/panLangScript.sml:42 *)
  panop = (* Div | *)Mul (* | Mod*)
```

`Div` and `Mod` are commented out of the constructor list, and `pan_op_def`
(`pancake/semantics/panSemScript.sml:191`) defines only `pan_op Mul [w1;w2] =
SOME(w1 * w2)` with `pan_op _ _ = NONE`. So to emit the divide-by-10 loop onto
the real target, each digit's quotient and remainder must be computed **by
repeated subtraction** (subtract 10 until the running value drops below 10,
counting iterations for the quotient, the residue for the remainder). That is
O(quotient) inner iterations per output digit versus a single hardware `DIV` —
the sympathy loss, in the hot path of every response's status line and
`Content-Length`.

**The upstream change it needs.** Uncomment `Div` and `Mod` in the `panop`
datatype; add the defining clauses `pan_op Div [w1;w2] = SOME (word_div w1 w2)`
and `pan_op Mod [w1;w2] = SOME (word_mod w1 w2)` to `pan_op_def`; then thread the
two new constructors through every compiler pass that matches on `panop` and its
correctness proof: `pan_to_crep`, `pan_to_word`, `pan_to_target`, and the proof
scripts `pan_to_crepProofScript.sml`, `pan_to_wordProofScript.sml`,
`pan_to_targetProofScript.sml`. On our side, extend `Pancake/Sem.lean`'s modelled
`Panop` and re-discharge the A1 faithfulness match for the new clauses.

**Why it must be upstream-coordinated.** It is a source-language change to the
verified compiler: it grows the AST the compiler is proven correct over, so
`compile_correct` must be re-proved across the enlarged operator set, end to end.
There is no way to "just use divide" without extending the TCB, and doing it
privately forks CakeML. It is the *smallest* such delta (the operators are
pre-reserved in the datatype, and `word_div`/`word_mod` already exist in the word
theory), which is why it ranks first — but it is still a verified-backend PR, not
a local edit.

**Honest not-now note.** The repeated-subtraction workaround is *correct and
proven* today at the spec level; it is merely slow. Nothing on the correctness
arc is blocked on `Div`/`Mod`. This is a later, upstream PR.

---

## Item 2 — packed / coalesced byte-store codegen

**The current workaround.** Two byte-write paths exist, and neither emits wide
aligned stores for a run of bytes:

- The **general** byte writer is `write_bytearray` (modelled in
  `Pancake/BytesModel.lean` §9 over `Pancake/Sem.lean`'s `putByte`), which is
  byte-at-a-time: `writeByteArray … base (b :: bs) = putByte … base b` then
  recurse on `base + 1`. Each `putByte` is a **read-modify-write of the enclosing
  word** (`get_byte`/`set_byte`/`byteAlign` on the word-addressed
  `memory : Word → Word`). Writing an N-byte region therefore costs N
  read-modify-write word operations instead of ⌈N/8⌉ aligned word stores — an
  ~8× store-traffic inefficiency plus a per-byte load dependency, in the render
  loop that emits every header line and the body.

- The only **wide-store** path is the `≤8-byte-per-word` stub: `packBE`
  (`Pancake/RealStageDemo.lean` §1) packs up to 8 bytes big-endian into one word
  and the fill loop `fillWhile` stores that whole word per slot (slot `k` at byte
  address `8·k`). This is fast but a **fixed stub** — one packed header word, not
  a general variable-length region packer, as the file's own §1 note records.

So today the render is either fast-but-stubbed or general-but-byte-serial.

**The upstream change it needs.** A verified **store-coalescing** capability: a
byte-array store of a statically- or dynamically-bounded run compiles to aligned
word stores (with masked head/tail for the unaligned ends), rather than a per-byte
`putByte` chain. In CakeML this lives in the byte-array store compilation across
`data_to_word` / `word_to_word`, and the optimization must carry its own
correctness theorem: the coalesced word-store sequence produces byte-for-byte the
same memory image as the byte-serial semantics (exactly the getByte-decomposition
relation our `Pancake/BytesModel.lean` already proves for a single word, lifted to
a region). Our side then retargets the render lowering onto the coalesced
primitive and re-proves the byte-effect over the region.

**Why it must be upstream-coordinated.** `write_bytearray`'s byte-at-a-time
behaviour is CakeML's actual `panSem` semantics; the *compilation* of it is a
verified backend pass. A coalescing optimization changes that pass and so must
re-discharge the pass-correctness proof — it is not something we can bolt on in
Lean without either forking the backend or losing the refinement. The wide-store
byte-decomposition algebra is already proven on our side for one word, so the
upstream lift is well-scoped, but it is still a proof-carrying backend change.

**Honest not-now note.** The byte-serial writer is correct and proven. The stub
packer covers the demo. Coalescing is pure throughput; it waits.

---

## Item 3 — a re-entrant / per-shard runtime ABI and entry

**The current workaround.** The emitted serve is an **export function**:
`serve(ctrl, req, len, resp)` under the SysV C ABI, with `cml_main` doing
runtime init (`crates/cake-serve/cake_serve_stub.c` models the contract for the
integration; `crates/dataplane/src/cake_serve.rs` is the host seam). Two shapes
are worked around:

- **Single-image runtime state.** The real emitted object keeps its heap/stack
  region and saved runtime state in **process-global data words**, so one image
  is single-threaded. To serve on N per-core reactor shards in parallel, the host
  links **N symbol-disjoint copies of the image** (or, in the stub,
  `__thread`-local region slots) so no two shard threads touch the same runtime
  state. This is duplication standing in for a re-entrant runtime; a thread that
  arrives after the image pool is exhausted falls through to the interpreted path
  (a named residual).

- **Main-return.** The entry is compiled to **return to the host** after init
  rather than run to program exit, so `serve` can then be called per request.
  This is a build-mode workaround around the default whole-program `main`.

- **Narrow export shape.** The static checker
  (`pancake/panStaticScript.sml`, `check_export_params_def`) requires every
  exported parameter to be `shape = One` (a single word) and caps exported
  functions at ≤4 arguments, so the C-callable boundary passes only words, never
  structs — the request/response cross the boundary as `(ptr, len)` words.

**The upstream change it needs.** First-class re-entrant runtime region slots
emitted per-instance (so one object is multi-shard-safe without N linked copies);
a supported, documented main-return / callable-entry mode as a first-class ABI
rather than a build flag; and, if the response path ever wants richer arguments,
relaxing `check_export_params` beyond the word-only ≤4-arg export shape. All of
these live in CakeML's `pan_to_target` runtime emission, the basis/runtime, and
the static checker, each with its proof.

**Why it must be upstream-coordinated.** The runtime-region emission, the
whole-program entry, and the export-parameter static rules are all part of the
verified compiler and its target-semantics proof. Faking re-entrancy with N
images or `__thread` slots in the *host* C is exactly the seam we want to delete;
deleting it means the emitted runtime itself becomes re-entrant, which is a
backend change carrying the runtime-correctness obligation. Doing it host-side
forever keeps an unverified duplication layer in the serving plane.

**Honest not-now note.** The N-image / thread-local workaround is parallel-safe
and correct today (the per-shard-heap property is load-bearing and tested). This
item removes an unverified duplication layer for elegance and shard-count
headroom; it is not a correctness gate.

---

## Item 4 — register allocation, cache shape, SIMD

**The current workaround.** None is needed for correctness — this is the residual
scalar-codegen overhead. The verified backend uses its proven register allocator
(`compiler/backend/reg_alloc/`, `word_allocScript.sml`), which is **correctness-
first, not tuned** for loop-carried cache behaviour, and the target backend has
**no SIMD / vector path at all** (there is no vector directory under
`compiler/backend/`; every emitted instruction is scalar general-purpose). The
render and copy loops therefore run one machine word at a time with a
correctness-driven allocation, which is the bulk of the constant-factor gap to
hand-tuned C.

**The upstream change it needs.** SIMD would require new verified vector
instructions in the target model and its assembler semantics, plus vector-aware
instruction selection, register allocation, and every backend pass proof extended
across them — the largest verified-TCB extension on this list. Cache-shape and
better allocation are tuning of CakeML's existing verified allocator and its
proof. All of it is inside the verified backend.

**Why it must be upstream-coordinated.** These are the verified compiler's own
backend and target semantics; there is no Lean-side or host-side substitute that
keeps the refinement. A private tuning fork loses upstream's ongoing proof
maintenance.

**Honest not-now note.** Lowest priority: biggest TCB delta, longest upstream
lead time, and it only shaves the constant factor. Correctness never depends on
it. Far-later.

---

## Ranked: the top three sympathy items and their upstream nature

1. **`Div` / `Mod` in the op set (Item 1).** Highest ROI, smallest delta: the
   operators are pre-reserved (commented out) in the `panop` datatype and
   `word_div`/`word_mod` already exist, so the upstream PR is "uncomment, define
   two `pan_op` clauses, thread two constructors through three passes and their
   proofs." Kills the repeated-subtraction divide-by-10 in every response's
   decimal render. **Upstream nature:** a source-language change to the verified
   compiler; re-proves `compile_correct` over the enlarged op set.

2. **Packed / coalesced byte stores (Item 2).** The byte-serial `write_bytearray`
   (one read-modify-write word op per byte) is the dominant inefficiency in the
   render loop that touches every header and the body; the only wide-store path is
   a fixed ≤8-byte stub. **Upstream nature:** a verified backend optimization
   (byte-array store compilation in `data_to_word`/`word_to_word`) that must carry
   a proof that coalesced aligned word stores yield the identical byte image —
   the single-word case of which we already prove in `BytesModel.lean`.

3. **Re-entrant / per-shard runtime ABI (Item 3).** Deletes the unverified
   N-image / `__thread` duplication currently faking per-shard heaps, and makes
   the callable-entry / main-return mode first-class. **Upstream nature:** changes
   CakeML's runtime-region emission, entry, and export-parameter static checker,
   each proof-carrying, in `pan_to_target` / basis / `panStaticScript`.

(Item 4 — register allocation / cache / SIMD — ranks below all three: largest TCB
delta, constant-factor-only, and no correctness dependency.)

---

## Residuals and honesty notes

- **Nothing here is scheduled now, by design.** This is the deferred track. It is
  captured so the sympathy work is not *lost*, not so it is *started*. The
  correctness arc (`TRANSLATOR-ARC.md`) comes first.
- **Grounding.** Every "current workaround" above is read off the built tree at
  the arc's current state: the commented-out `panop = (* Div | *)Mul (* | Mod*)`
  and `pan_op_def` (CakeML `ed31510b3`); the divide-by-10 spec loop and its
  axiom-clean `natToDec_readback` (`Pancake/SerializeCompile.lean`); the
  byte-serial `write_bytearray` and the `≤8-byte-per-word` `packBE` stub
  (`Pancake/BytesModel.lean` §9, `Pancake/RealStageDemo.lean` §1/§3); the export
  ABI, main-return, and process-global region slots
  (`crates/cake-serve/cake_serve_stub.c`, `crates/dataplane/src/cake_serve.rs`);
  the word-only ≤4-arg export static rule (`pancake/panStaticScript.sml`,
  `check_export_params_def`); and the absence of any vector path under
  `compiler/backend/`.
- **Faithfulness.** No invented compiler primitives. `Div`/`Mod`/`word_div`/
  `word_mod`, `write_bytearray`, `pan_op`, `check_export_params`, `reg_alloc`,
  and the export/main-return ABI are all real CakeML/Pancake constructs at the
  pinned revision.
- **Not verified here.** This is a backlog document; it introduces no theorem and
  changes no code, so there is no build to run for it. The proven facts it cites
  (e.g. `natToDec_readback` axiom-clean) are the *existing* results recorded in
  the arc and its build scripts; this pass did not re-run those builds.
- **Open estimation residual.** The upstream-review latency and the exact
  proof-effort per item are not estimated here — they need an upstream-facing
  scoping pass with the CakeML maintainers before any of this is picked up.
