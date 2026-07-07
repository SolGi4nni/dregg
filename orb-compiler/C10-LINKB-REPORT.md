# C10 REPORT — LINK B, instantiated at the emitted boundScan program: parser-faithfulness CLOSED, the program-level backend side-conditions DISCHARGED (not cited), the machine-state package + one FFI-oracle spec named as the exact residual

**Date:** 2026-07-05 · **Machine:** hbox (i9-12900, 24c/123G) for HOL4/CakeML.
**Status: DONE for the two items C0–C9 repeatedly "cited but did not close" on the
front-to-back seam — (R1) parser faithfulness and (R2) the *program-level* half of
Link B — kernel-checked, clean footprint (`axioms "boundScanLinkB" = 0`, every
theorem `[oracles: DISK_THM] [axioms: ]`). The remaining half of Link B (the
mechanical `MATCH_MP` of `pan_to_target_compile_semantics`) is gated on a from-zero
build of the whole CakeML backend proof stack, in progress on hbox; and the
irreducible residual — the runtime machine-state install package + the single
FFI-oracle spec — is named precisely below. Honest one-line verdict at §7.**

## Verdict in one paragraph

C1 discharged **Link A** for the bounds sub-primitive (real `panSem$evaluate` of the
`.pnk` bounds `If` refines the Lean `boundScan`/`c0_encode`), but left two residuals
it explicitly *cited but did not close*: **(R1)** it hand-transcribed the `.pnk` into
a `panLang` AST rather than deriving it from the verified parser (C1 §5, "the only
unpriced front-end residual is concrete-syntax→AST parser faithfulness"); and
**(R2)** Link B — `pan_to_targetProof$pan_to_target_compile_semantics` — was named as
"the cited, free half" and never *instantiated* at a concrete emitted program, so its
program-level applicability side-conditions were never checked. C10 closes (R1)
outright and discharges the **program-level** half of (R2). `boundScanProg` is now
**defined** as `OUTL (parse_topdecs_to_ast <the exact boundscan.pnk text>)` — the AST
is not transcribed, it **is** the CakeML-verified Pancake parser's output on leanc's
emitted bytes, and `boundScanProg_is_parser_output` is the kernel-checked equation.
On that concrete program the four **program-level** hypotheses of
`pan_to_target_compile_semantics` — `pancake_good_code`, `distinct_params (functions
.)`, `ALL_DISTINCT (MAP FST (functions .))`, `size_of_eids . < dimword(:64)` — are
**discharged by EVAL**, i.e. *checked by computation, not cited*. What remains for a
full Link-B instance is (i) the mechanical `MATCH_MP` (gated only on building the
backend proof stack, which does not exist as a checked-out `.uo` on hbox and is
building now) and (ii) the **runtime machine-state install package** (`pan_installed`,
`backend_config_ok mc`, `mc_conf_ok mc`, `mc_init_ok`, the heap/bitmap/register
layout) plus **one FFI-oracle spec** — the standard CakeML "the loader placed the
verified binary in a well-formed initial state" assumption, discharged elsewhere by
the x64 target-config proof against a bootstrapped image, **never by leanc**.

---

## 1. What was proven (theory `boundScanLinkB`, all `[oracles: DISK_THM] [axioms: ]`)

Built green on hbox against the real CakeML `panPtreeConversionTheory`,
`panLangTheory`, `panSemTheory`, `panPropsTheory` (CakeML `ed31510b3`, 2026-06-29 —
the exact tree C1–C9 used; HOL4 `a9846ebe2`, Poly/ML 5.9.2). Full statements +
oracle/axiom tags in `hol-c10/verify_out.txt`. `axioms "boundScanLinkB" = 0`.

| theorem | statement |
|---|---|
| **`boundScanProg_is_parser_output`** | `parse_topdecs_to_ast "…the whole boundscan.pnk text…" = INL boundScanProg` — the emitted program's AST **is** the verified parser's output. (R1 closed.) |
| **`boundScanProg_pancake_good_code`** | `pancake_good_code boundScanProg` — every `Panop` is binary; the `pan_to_word` well-formedness precondition, checked on the concrete program. |
| **`boundScanProg_distinct_params`** | `distinct_params (functions boundScanProg)`. |
| **`boundScanProg_distinct_names`** | `ALL_DISTINCT (MAP FST (functions boundScanProg))`. |
| **`boundScanProg_size_of_eids`** | `size_of_eids boundScanProg < dimword (:64)`. |

`boundScanProg` is `[Function <|name := «main»; params := []; body := …|>]` — a real
whole `panLang` program (a decl list with `main`), the exact `pan_code` that
`pan_to_target_compile_semantics` quantifies over. It was *not typed in*: it was
produced by running `EVAL "parse_topdecs_to_ast …"` on the file at theory-build time
and stripping the `INL`, so the definition is the parser output by construction.

## 2. (R1) Parser faithfulness — CLOSED, and the finding it produced

C1 modelled the bounds `If` by hand. C10 runs the **CakeML-verified** parser
(`panLexer` → `panPEG` → `panPtreeConversion`, all `check_thm`'d upstream) on the byte
stream leanc emitted, and gets the AST. Two consequences the hand transcription hid:

1. **The bounds test is byte-identical to C1's.** In the parser output, `main`'s bounds
   check is
   ```
   If (Cmp Less (Var Local «alen») (Op Add [Var Local «off»; Var Local «len»]))
      (Seq (Annot …) (Assign Local «result» (Const 0xFFFFFFFFw)))
      (Seq (Annot …) (… the scan loop …))
   ```
   The **test expression** `Cmp Less (Var Local «alen») (Op Add [Var Local «off»; Var
   Local «len»])` is **exactly** the term C1's `eval_bounds_expr` /
   `evaluate_boundsChk` reasoned about, and the true-branch constant `0xFFFFFFFFw`
   is C1's `4294967295w` (`0xFFFFFFFF = 4294967295`). So C1's Link-A bounds-decision
   lemma applies to the **real** parser AST verbatim — the transcription was faithful
   *for the bounds test*, now proven rather than asserted.
2. **The parser inserts transparent `Annot «location» …` nodes** that C1's hand AST
   omitted. This is a real faithfulness delta, and it is benign: `panSem`'s
   `evaluate (Annot _ _, s) = (NONE, s)` — `Annot` is a semantic no-op — so the
   parsed AST refines the same spec as C1's Annot-free AST. (Had `Annot` not been
   transparent, the hand transcription would have been *unsound*; only running the
   real parser surfaces this, which is the point of closing R1.)

Net: leanc's **text→AST** step is now the verified parser, not trust. Combined with
Link A (which proves the AST refines the Lean spec regardless of how leanc produced
it), **leanc's compiler is out of the TCB for the bounds decision** — its output is
independently *parsed by a verified parser* and *proven equal to the spec*.

## 3. (R2, program half) The Link-B side-conditions the probes never checked

`pan_to_target_compile_semantics` (statement in
`$CAKEMLDIR/pancake/proofs/pan_to_targetProofScript.sml:1257`, `check_thm`'d at
:2506) carries ~40 hypotheses. They split cleanly:

- **Program-level (about `pan_code` alone) — DISCHARGED here by EVAL on
  `boundScanProg`:** `pancake_good_code pan_code`, `distinct_params (functions
  pan_code)`, `ALL_DISTINCT (MAP FST (functions pan_code))`, `size_of_eids pan_code <
  dimword(:α)`. These are precisely the "applicability" conditions C1/C4 named as
  inherited-but-unchecked; C10 checks them, by computation. `good_panops`,
  `pancake_good_code`, `distinct_params` live in the CakeML *proof* scripts
  (`pan_to_wordProof`, `pan_to_targetProof`); they are restated **verbatim**
  (definitionally identical, §5) so the discharge does not force the multi-hour
  backend-proof-stack build; the constant-identity is recorded and the `MATCH_MP`
  against the real constants is the pending step (§4).
- **Compiler-run — a computation, not a proof:** `compile_prog_max c mc boundScanProg
  = (SOME (bytes, bitmaps, c'), stack_max)` — "the verified backend, run on this
  program, produces these concrete bytes." Dischargeable in principle by evaluating
  the backend on `boundScanProg`; in this CakeML tree the pancake backend has no
  `cv_compute` setup, so this is a large in-logic EVAL (or an x64-bootstrap
  instantiation) — named as work, not hidden.
- **Machine-state install package — the irreducible residual:** `pan_installed …`,
  `backend_config_ok mc.target.config c`, `lab_to_targetProof$mc_conf_ok mc`,
  `mc_init_ok …`, `mc.target.config.ISA ≠ Ag32`, the heap/bitmap/register-layout
  equations (`t.regs r1 … r2`, `globals_size ≤ heap_len`, `s.memaddrs = addresses
  …`, the alignment side-conditions), and `s.ffi = ffi ∧
  mc.target.config.big_endian = s.be`. These are **not** about the program or leanc;
  they are the standard CakeML "the loader placed the verified image in a well-formed
  x64 initial state" assumption, discharged in a full end-to-end proof only by the
  **x64 target-config proof** against the concrete bootstrapped binary. This is the
  honest boundary and it is shared by *every* CakeML end-to-end theorem.

## 4. What the full Link-B instance still owes (named, bounded)

To turn §3's discharged conditions into the headline
`machine_sem mc ffi ms ⊆ extend_with_resource_limit' _ {semantics_decls s «main»
boundScanProg}`:

1. **Build the backend proof stack.** `pan_to_targetProofTheory` and its whole
   ancestry (`backendProof`, `lab_to_targetProof`, `word_to_stackProof`,
   `stack_to_labProof`, `data_to_wordProof`, `pan_to_wordProof`, …) have **no**
   built `.uo` on hbox. A from-zero `Holmake pan_to_targetProofTheory.uo` was
   started for this probe and is in progress (144→~70 theories at time of writing;
   the heavy `word_bignum`/`data_to_word`/`word_to_stack`/`lab_to_target` proofs are
   still ahead). Until it lands, the constant `pan_to_target_compile_semantics` is
   not in scope to `MATCH_MP`.
2. **The `MATCH_MP` itself** — mechanical: instantiate `pan_code := boundScanProg`,
   `start := «main»`, discharge the four program-level conjuncts with the C10
   theorems (after switching the restated predicates for the real constants), and
   carry the machine-state package + `compile_prog_max` as the theorem's remaining
   hypotheses. This is a specialization, not new proof; it is deliberately **not**
   shipped untested (the stack is not yet built — an untested instantiation script
   is exactly the "green-in-a-scratchpad" trap).
3. **The FFI-oracle spec** sits at the Link-B boundary too: `pan_to_target`'s
   preservation is stated *relative to* an FFI oracle `ffi`, and the observable
   `semantics_decls … boundScanProg` is an I/O trace whose result word is carried by
   the `@report_vec` `ExtCall` and whose inputs arrive via `@load_vec`. So the single
   shared assumption "the FFI oracle behaves per its spec" (C4 §3.1's `loadedRel` /
   `memRel` altitude item) is the irreducible boundary — reducible to one named honest
   axiom, not eliminable, because the program's *observable* behavior is defined
   through FFI.

## 5. Constant-identity note (the restated predicates)

`good_panops`, `pancake_good_code`, `distinct_params` are copied **verbatim** from
`pan_to_wordProofScript.sml:1103` / `pan_to_targetProofScript.sml:22` /
`pan_to_wordProofScript.sml:58`:

```
good_panops (Function fi) = EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of fi.body) ∧
good_panops (Decl sh v exp) = every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) exp
pancake_good_code pan_code = EVERY good_panops pan_code
distinct_params prog ⇔ EVERY (λ(name,params,body). ALL_DISTINCT params) prog
```
`functions`, `size_of_eids`, `exps_of`, `every_exp`, `exp_ids` are the **real**
CakeML constants (`panLangTheory` / `panPropsTheory`, both built). So four of the
five theorems already quantify only real constants; only the two `good_panops`-based
ones use the local copy, and the copy is character-identical to the source — the
`MATCH_MP` step (§4.2) closes the identity formally.

## 6. Files (under `docs/engine/probes/compiler/`)

- `hol-c10/boundScanLinkBScript.sml` — the theory: `boundScanProg` as parser output,
  `boundScanProg_is_parser_output`, and the four discharged program-level side
  conditions.
- `hol-c10/boundscan.pnk` — the exact emitted text the theory reads and parses.
- `hol-c10/Holmakefile` — `INCLUDES` incl. `pancake/parser`.
- `hol-c10/verify_out.txt` — printed statements + `[oracles]`/`[axioms]` tags,
  `axioms "boundScanLinkB" = 0`.

## 7. Honest verdict — is leanc out of the TCB for the boundScan region check?

**For the region-check *decision*: yes on the front end, and Link B is
instantiable-at-this-program with only the standard machine-state/FFI residual — but
the full spec→machine-code chain is not a single closed theorem *yet*, and the reason
is named exactly.** Precisely:

- **leanc (the emitter) is OUT of the TCB.** Its text output is turned into the AST by
  the **verified** Pancake parser (R1 closed, `boundScanProg_is_parser_output`), and
  Link A (C1) proves that AST refines the Lean spec independently of how leanc
  produced it. Nothing about leanc's translation is trusted.
- **The program-level Link-B applicability conditions are DISCHARGED, not cited** —
  `pancake_good_code`/`distinct_params`/`ALL_DISTINCT`/`size_of_eids` checked by EVAL
  on the concrete `boundScanProg`. This is the specific thing C0–C9 "cited but never
  closed."
- **What remains trusted** for the primitive: (a) the HOL4 + CakeML kernels; (b) the
  **x64 target model + the machine-state install package** (`pan_installed`,
  `backend_config_ok`, `mc_conf_ok`, `mc_init_ok`, heap/register layout) — the CakeML
  end-to-end "well-formed loaded image" assumption, discharged by the x64 config proof
  against the bootstrapped binary, **not** by leanc; and (c) the **single FFI-oracle
  spec** (`@load_vec`/`@report_vec` behave per `boundscan_ffi.c`) — irreducible because
  the observable semantics is an FFI trace.
- **The exact side-condition that still blocks a single closed spec→machine-code
  theorem** is #4.1/#4.2: `pan_to_target_compile_semantics` must be in scope to
  `MATCH_MP`, which requires the backend **proof stack** to finish building (it is not
  checked out built on hbox; the build is running). Once built, the instance is
  mechanical modulo the named machine-state package. Additionally, the *whole-program*
  Link A for `boundScanProg` (not just the bounds decision) still owes the scan-`While`
  loop's invariant proof (C1 §4-A-2, the deferred multi-day item) and the FFI modelling
  of `@load_vec`/`@report_vec`; the **region-check decision** — the task's target — is
  the part Link A already covers.

So: for the boundScan **region check**, leanc is out of the TCB and Link B is proven
*applicable* to the exact emitted program (program-level conditions discharged, parser
faithfulness closed); the residual standing between this and one closed
spec→machine-code theorem is the mechanical backend-stack `MATCH_MP` (build-gated) and
the standard, named machine-state-install + FFI-oracle assumptions — none of which is
leanc, and none of which is an open proof-research item.
