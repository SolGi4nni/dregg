# C1 REPORT — Link A paid down for the bounds sub-primitive: the first real preservation theorem instance against `panSem$evaluate`

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**Status: DONE for the bounds sub-primitive — four kernel-checked HOL4 theorems
against the REAL Pancake source semantics; scan-loop + memory relation remain,
priced. Zero cheats, zero oracles, zero axioms.**

## Verdict in one paragraph

C0 dual-emitted the region bounds-check + byte-scan and *priced* Link A (the
front-end obligation: Lean/HOL4 SPEC ⇔ panLang source semantics) without paying
it. C1 pays it down for the **bounds-check sub-primitive**. The deliverable is
a HOL4 theory (`boundScanLinkAScript.sml`) that proves, against the **actual
`panSem$evaluate` / `panSem$eval` of the CakeML tree** (not C0's behavioral
twin), that running the `.pnk` bounds `If` refines the Lean model function
`boundScan` / `c0_encode`: `panSem$eval` of the bounds expression returns `1w`
**exactly** when the Lean spec says out-of-bounds (`boundScan = NONE`), and
`panSem$evaluate` of the `If` writes the sentinel `c0_encode NONE = 0xFFFFFFFF`
into `result` on exactly the out-of-bounds inputs and leaves the state untouched
otherwise. Four theorems, all `[oracles: DISK_THM] [axioms: ]` — no `cheat`, no
`new_axiom`, no SMT/other oracle: genuine HOL4 kernel proofs. This is the FIRST
real **Lean-model-step → panLang-semantics** preservation instance for the
compiler lane. What it is **not**: the whole primitive. The scan `While` loop
and its `LoadByte` memory relation — C0 §4-A items 2 and 3, the multi-day part —
are **not** proven here; they are the honest remaining cost, restated below with
the new information C1 produced. C1 also produced a **finding C0's twin could not
see**: the emitted bounds test is a **signed** comparison, so its correctness
carries a signed-range side condition — the P2 §4.2 convention seam, which
C0 declared "does not bite," in fact **does** bite for the comparison (it just
does not bite for the digest fold C0 was looking at).

---

## 1. What was proven (against the real `panSem`)

Theory `boundScanLinkA`, built with `Holmake` green against the just-built
`panSemTheory` (the real Pancake operational semantics), CakeML `ed31510b3`
(2026-06-29), HOL4 `a9846ebe2` (2026-07-02), Poly/ML 5.9.2. All four theorems
carry `[oracles: DISK_THM] [axioms: ]` — the HOL4 analogue of the Lean
`#print axioms` clean-footprint check (`DISK_THM` is the serialization tag, not
a soundness oracle; the absence of any custom oracle or extra axiom is the
point). Full statements in `hol-c1/verify_out.txt`.

**The Lean SPEC (re-declared in HOL, byte-identical to C0's twin):**
`boundScan a off len = if off+len ≤ LENGTH a then SOME (scanFrom …) else NONE`;
`c0_encode NONE = 4294967295`, `c0_encode (SOME k) = k`.

**The IMPLEMENTATION fragment** `boundsChk` — the `.pnk` bounds `If`, as a real
`panLang$prog` term (`Cmp Less` = the SIGNED test Pancake `<` compiles to; the
else-branch is `Skip`, a stand-in for the scan loop which is out of scope):
```
If (Cmp Less (Var Local «alen»)
             (Op Add [Var Local «off»; Var Local «len»]))
   (Assign Local «result» (Const 4294967295w))
   Skip
```

**`stRel a off len r0 s`** — the state/memory relation: `s.locals` holds
`n2w (LENGTH a)`, `n2w off`, `n2w len` at the three names and a declared word
`r0` at `result`, and the sizes fit the signed range (`LENGTH a < 2^63`,
`off+len < 2^63`).

| theorem | what it says (the refinement) |
|---|---|
| **`signed_lt_n2w64`** | `x,y < 2^63 ⇒ ((n2w x : word64) < n2w y ⇔ x < y)` — the convention lemma: on the non-negative signed range the SIGNED word order agrees with ℕ order. This is where an off-by-a-sign-bit bug would live. |
| **`eval_bounds_expr`** | `stRel … ⇒ eval s (Cmp Less (Var «alen») (Op Add [Var «off»; Var «len»])) = SOME (ValWord (if boundScan a off len = NONE then 1w else 0w))`. The core: real `panSem$eval` of the bounds expression = `1w` **iff** the Lean spec says out-of-bounds. |
| **`evaluate_boundsChk`** | `stRel … ⇒ evaluate (boundsChk, s) = (NONE, if boundScan a off len = NONE then set_var «result» (ValWord (n2w (c0_encode (boundScan a off len)))) s else s)`. End-to-end: real `panSem$evaluate` of the `If` writes the Lean-encoded sentinel exactly on out-of-bounds inputs. |
| **`boundsChk_encodes_spec`** | the same in the report's vocabulary: `∃s'. evaluate (boundsChk,s) = (NONE,s') ∧ (out-of-bounds ⇒ result = n2w (c0_encode (boundScan …))) ∧ (in-bounds ⇒ s' = s)`. |

These are equations whose LHS is the **actual** `panSem` `eval`/`evaluate` on the
**actual** panLang AST and whose RHS is the **Lean model** function. That is the
Link-A shape C0 defined ("`semantics_decls … pan_code` … returns a result word
equal to `encode (boundScan a off len)`"), discharged for the bounds decision.

## 2. The finding: the bounds test is SIGNED, and the convention seam bites

C0 §4-A-4 wrote that the P2 §4.2 floor-vs-Euclidean / signed-vs-unsigned seam
"does not bite because there is no division and no negative value on the path."
That is true **for the digest fold** (`& 16777215`, `* 31`, `+`, all in-range).
C1 shows it is **not** the whole story for the *comparison*: tracing the real
`panPtreeConversion`, the Pancake token `<` is `LessT`, which maps to
`(Less, F)` — **`Cmp Less`, the SIGNED `asm$word_cmp Less w1 w2 = (w1 < w2)`**
(HOL `word_lt`). (`<+` would be the unsigned `Lower`.) So the emitted bounds
check is a signed word comparison, and an honest Link A for it **must** carry a
signed-range hypothesis: the arena size and the view extent must fit the
non-negative signed range (`< 2^63` on the 64-bit target), or a length with the
top bit set would read as negative and the check would invert. That hypothesis
is exactly the `LENGTH a < 2^63 ∧ off+len < 2^63` conjuncts of `stRel`, and
`signed_lt_n2w64` is the witness lemma that discharges it. C0's `num`-based
behavioral twin (`boundScanScript.sml`, `≤` over `num`) **could not** surface
this — it is precisely the kind of thing that only appears when you prove
against the real word-typed `panSem`, which is the point of paying Link A rather
than resting on kernel-checked testing. Concrete consequence for the engine: any
region whose length could exceed `2^63` needs `<+` (unsigned) in the `.pnk`, not
`<`; with `<` the correctness theorem legitimately requires the size bound.

## 3. What this discharges of C0 §4's Link-A itemization

C0 split Link A into five pieces. C1 closes the ones the bounds sub-primitive
touches and sharpens the estimate on the rest:

- **§4-A-1 (the bounds `If`).** C0 called this "the small instance I *could*
  have closed" and did not. **C1 closes it** — both arms — as
  `eval_bounds_expr` + `evaluate_boundsChk`, against real `panSem`, plus the
  word-convention lemma C0 did not name (the signed-range one).
- **§4-A-4 (word/int conventions).** The `+` (`Op Add` ⇒ `word_add`, via
  `word_add_n2w`) and the comparison (`Cmp Less` ⇒ `word_lt`) each got their
  worked convention treatment. New over C0: the comparison's **signed** nature
  and its side condition (§2 above) — the adversarial witness content P2 §4.2
  mandates, now concrete.
- **§4-A-5 (the `encode` injection).** Discharged inside `evaluate_boundsChk`
  (`4294967295w = n2w 4294967295`, the sentinel identity).
- **§4-A-2 (the scan `While`).** **NOT done.** Still the load-bearing item: a
  Hoare-style loop-invariant proof over `panSem`'s clocked `While` clause
  (`acc = scanFrom a off i 0 ∧ pos = off+i ∧ i ≤ len`, induction on `len−i`).
- **§4-A-3 (`LoadByte` / memory relation).** **NOT done.** The lemma relating
  `panSem`'s word-addressed byte memory (`mem_load_byte`,
  `s.memory : α word → α word_lab` over `s.memaddrs`) to the Lean `Array UInt8`
  at `buf` — P2 §4.7's shape, still unbuilt.

## 4. Honest remaining cost, re-estimated with C1's information

The bounds decision — a data-dependent `If` over a `Cmp`/`Op`/`Var` expression
with a word-convention side lemma — took, end to end against real `panSem`, on
the order of **a few hours** of proof-engineering (most of it spent finding the
signed-comparison fact and the `WORD_LT` + `word_msb_n2w` + `NOT_BIT_GT_TWOEXP`
recipe for `signed_lt_n2w64`, both now reusable). That confirms C0's "each word
op is tractable, mechanical" for the non-looping parts.

The **scan loop + memory relation (§4-A-2/3) remain the dominant cost** and C1
did not reduce them: they are a genuine loop-invariant induction over the
clocked `While` clause plus a first build of the byte-memory relation. C0
estimated "plausibly several days for even this 40-line program"; C1 gives no
reason to lower that — the loop is untouched — but it does **de-risk** it: the
expression/word-op/encode machinery underneath the loop body is now proven, so
the loop proof inherits a working `eval`-reduction + convention toolkit and only
owes the induction and the memory lemma. Revised honest number: **the bounds
decision is paid (hours); the digest loop is the remaining multi-day item, now
sitting on a proven expression layer.**

## 5. `leanc`-out-of-TCB verdict for this primitive

Unchanged in structure from C0, now with the front-end half partially real:

- **Backend (Link B).** Still inherited: `pan_to_target_compile_semantics`
  (`check_thm`'d in the CakeML tree) deletes `cake`'s codegen, `cc`'s optimizer,
  and `rustc`/`leanc` from the TCB for the compiled Pancake. C1 does not re-do
  this; it remains the cited, free half.
- **Front-end (Link A).** For the **bounds sub-primitive**, Link A is now a
  discharged HOL4 theorem against `panSem` source semantics — **not** kernel-
  checked testing. So for the bounds decision specifically, the claim "the Lean
  model and the source the verified backend consumes agree" is *proven*, and the
  only residual front-end trust is the **hand-transcription of the `.pnk` `If`
  into the `panLang` AST** (`boundsChk_def`): C1 modelled the AST by hand rather
  than running the Pancake **parser** theory (`panPtreeConversion`) to derive it
  from the concrete syntax. Closing that (parse the `.pnk`, prove the parser
  output equals `boundsChk`) is a small, named, separate step — the honest
  residual for this primitive.
- **Still outside any theorem:** the FFI (`basis_ffi.c` + `boundscan_ffi.c`, the
  arena-encoding oracle) and the target ISA model — exactly as C0 stated.

Net: for the bounds check, the front-end preservation is real, the backend is
inherited, and the only unpriced front-end residual is concrete-syntax→AST
parser faithfulness (small) — the digest loop's Link A is the remaining
substantive work.

## 6. Files (under `docs/engine/probes/compiler/`)

- `hol-c1/boundScanLinkAScript.sml` — the theory: the Lean SPEC re-declared, the
  `boundsChk` AST, `stRel`, and the four theorems with full proofs. Self-
  contained modulo the CakeML `panSem`/`panLang` ancestors.
- `hol-c1/Holmakefile` — `INCLUDES` pointing at the CakeML `pancake`,
  `pancake/semantics`, `compiler/backend`, `compiler/encoders/asm`, `misc`,
  `semantics/ffi` dirs.
- `hol-c1/verify_out.txt` — the printed theorem statements + `[oracles]`/
  `[axioms]` tags (the clean-footprint evidence).

## 7. Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 built at `~/src/HOL`:
```
export CAKEMLDIR=$HOME/src/cakeml
export PATH=$HOME/src/HOL/bin:$PATH
cd $CAKEMLDIR/pancake/semantics && Holmake panSemTheory.uo   # ~30 s, deps incl.
# copy hol-c1/{Holmakefile,boundScanLinkAScript.sml} into a work dir, then:
cd <workdir> && Holmake boundScanLinkATheory.uo              # green, [1/1] OK
```
`panSemTheory` and its dependency chain (misc, ffi, asm, wordLang, panLang)
build from the CakeML tree in well under a minute on hbox; the C1 theory itself
compiles in ~5 s.

## 8. Bottom line for Phase C

The compiler lane's front-end obligation is no longer only priced — for the
bounds-check sub-primitive it is **paid**, with a real Lean-model-step →
`panSem`-source-semantics theorem, kernel-checked, no oracles. The exercise also
corrected a C0 nuance (the comparison is signed; the convention seam bites for
the bounds test) — the kind of correction that only a real refinement, not a
behavioral round-trip, can produce. The remaining unit cost is now sharply
localized: **the digest `While` loop + its byte-memory relation**, sitting on a
proven expression/word-op layer, is the multi-day item; everything around it for
this primitive is done.
