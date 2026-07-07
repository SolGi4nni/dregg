# C11 REPORT — LINK B, the build-gated MATCH_MP CLOSED: `pan_to_target_compile_semantics` instantiated at the concrete emitted `boundScanProg`, program-level side conditions discharged against the REAL backend constants, one kernel-checked theorem — and the EXACT residual for a single spec→machine-code theorem named precisely

**Date:** 2026-07-06 · **Machine:** hbox (i9-12900, 24c/123G) for HOL4/CakeML.
**HOL4 `a9846ebe2` (Trindemossen 2, stdknl), CakeML `ed31510b3`** — the exact
tree C1–C10 used. **Status: the specific `MATCH_MP` the C10 report named as the
one build-gated pending step (C10 §4.1/§4.2) is DONE.** `boundScanProg_linkB` is
kernel-checked, `[oracles: DISK_THM] [axioms: ]`, `axioms "boundScanLinkBInst" =
0`, 0 cheats. It is the **real** `pan_to_targetProof$pan_to_target_compile_semantics`
specialized to the concrete emitted program, with the four program-level side
conditions discharged against the **real** backend constants (not the C10 restated
copies). **Honest verdict at §5:** the *backend* half of the spec→machine-code
chain is now one closed theorem at the concrete program; the single *end-to-end*
spec→machine-code theorem for the whole primitive is **not** closed, and the exact
remaining item is **whole-program Link A** (the scan-`While` loop invariant + the
`@load_vec`/`@report_vec` FFI-trace refinement) — a front-end obligation, **not**
the backend and **not** leanc.

---

## 1. What C11 did (and the build surprise)

**The backend proof stack was already fully built on hbox.** The C10 report
recorded a from-zero `Holmake pan_to_targetProofTheory.uo` "in progress (144→~70
theories)". That build had **completed** (it left stale lock files dated 14:42 the
prior day but all objects present). `Holmake pan_to_targetProofTheory.uo`
returns immediately **up-to-date**; every needed proof theory is present as a
built `.uo`:

```
pan_to_targetProof  pan_to_wordProof  backendProof  lab_to_targetProof
word_to_stackProof  data_to_wordProof  stack_to_labProof     (all .hol/objs/*.uo)
```

So the ~1–2h from-zero build was **not** re-incurred (I cleared the stale locks
and confirmed up-to-date). C11 is the instantiation the C10 stack could not reach
because, at C10 time, `pan_to_target_compile_semantics` was not yet a built
constant in scope.

## 2. The closed theorem — `boundScanProg_linkB` (theory `boundScanLinkBInst`)

`[oracles: DISK_THM] [axioms: ]`, kernel-checked, 0 axioms. Built green in 15s
against the pre-built stack (`hol-c11/build_c11.log`). Full statement +
tags in `hol-c11/verify_out.txt` / `hol-c11/tags_out.txt`.

The instantiation (script `hol-c11/boundScanLinkBInstScript.sml`):

```
pan_to_target_compile_semantics
  |> INST_TYPE [alpha |-> “:64”]                       (* x64 word width          *)
  |> Q.INST [‘pan_code’ |-> ‘boundScanProg’,           (* the emitted program     *)
             ‘start’    |-> ‘«main»’]                   (* its entry point         *)
  |> SIMP_RULE bool_ss                                  (* discharge the 4 conjuncts *)
       [boundScanProg_pancake_good_code, boundScanProg_distinct_params,
        boundScanProg_distinct_names,   boundScanProg_size_of_eids]
```

where `boundScanProg` is **re-derived here as the CakeML-verified parser's output**
on leanc's exact `boundscan.pnk` bytes (`boundScanProg_is_parser_output`, identical
to C10's program), and the four program-level conditions are re-proven **against the
REAL backend constants** — `pancake_good_code` (`pan_to_targetProofTheory`),
`distinct_params` / `good_panops` (`pan_to_wordProofTheory`), `functions` /
`size_of_eids` (`panLangTheory`) — by EVAL. This is the constant-identity step C10
§5 deferred to "the `MATCH_MP` against the real constants": now performed.

Resulting theorem (verbatim, abbreviated antecedent — full text in `verify_out.txt`):

```
⊢ compile_prog_max c mc boundScanProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
  s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
  FDOM s.eshapes = FDOM (get_eids (functions boundScanProg)) ∧
  backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
  mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
  … the heap/bitmap/register-layout + alignment equations … ∧
  s.ffi = ffi ∧ (mc.target.config.big_endian ⇔ s.be) ∧
  OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
  pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
                (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
                (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs ∧
  semantics_decls s «main» boundScanProg ≠ Fail ⇒
  machine_sem mc ffi ms ⊆
  extend_with_resource_limit'
    (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
    {semantics_decls s «main» boundScanProg}
```

**The four program-level conjuncts are GONE from the antecedent** — proven for
`boundScanProg` and simplified away. What remains is exactly the standard CakeML
end-to-end residual. This is the `MATCH_MP` C0–C10 "cited but did not close".

## 3. What remains trusted in `boundScanProg_linkB` (the exact residual)

None of these is leanc. Each is a conjunct of the theorem's antecedent:

1. **HOL4 + CakeML kernels.** `[oracles: DISK_THM]` = the theorem is a kernel
   derivation carried through disk-cached theories (the built backend proof). No
   `cheat`, no axiom.
2. **The machine-state install package** — `backend_config_ok mc.target.config c`,
   `mc_conf_ok mc`, `mc_init_ok …`, `mc.target.config.ISA ≠ Ag32`, the
   register-layout (`len_reg`/`ptr2_reg`/`len2_reg`), heap/bitmap layout
   (`heap_len`, `globals_size`, `s.top_addr`, `s.memaddrs`), the alignment
   side-conditions, and `pan_installed …`. The standard CakeML "the loader placed
   the verified image in a well-formed x64 initial state" assumption, discharged in
   a full end-to-end proof by the **x64 target-config proof against the bootstrapped
   binary**, never by leanc; shared by *every* CakeML end-to-end theorem.
3. **`compile_prog_max c mc boundScanProg = (SOME (bytes,bitmaps,c'),stack_max)`** —
   the verified backend **run** on `boundScanProg`, binding the concrete machine
   `bytes`. A *computation*, not trust: dischargeable by evaluating the verified
   backend on the program (in this tree the pancake backend has no `cv_compute`
   setup, so this is a large in-logic EVAL or an x64-bootstrap instantiation). Until
   run to concrete bytes, `bytes` is a bound variable — the theorem holds for
   *whatever* the verified backend emits.
4. **The single FFI-oracle spec** — `s.ffi = ffi` and `ffi_names` all `ExtCall`:
   the observable `semantics_decls … boundScanProg` is an I/O trace whose result
   word is carried by `@report_vec` and inputs arrive via `@load_vec`. One named
   honest assumption, irreducible because the observable behavior *is* an FFI trace.
5. **`semantics_decls s «main» boundScanProg ≠ Fail`** — the source program does
   not itself diverge-to-Fail; the standard non-failure hypothesis.

## 4. The composition (task step 3) — why it does NOT close into one theorem, exactly

The task asked to compose "spec ⟺ panSem(`boundScanProg`) (Link A)" with
"panSem ⟺ machine-code (Link B)". **The premise is not met by the existing Link
A.** C1's Link A (`hol-c1/boundScanLinkAScript.sml`) proves refinement only for the
**bounds-decision fragment** — `boundsChk`, the `If` with the scan loop replaced by
`Skip` — at the `panSem$evaluate` (functional state-transformer) level:

```
evaluate (boundsChk, s) = (NONE, if boundScan a off len = NONE
                                  then set_var «result» (ValWord (n2w (c0_encode …))) s
                                  else s)
```

`boundScanProg_linkB`'s conclusion is stated over `semantics_decls s «main»
boundScanProg` — the **whole-program FFI-trace** semantics of the entire program
(the scan `While` loop and the `@load_vec`/`@report_vec` FFI included). These are
**different semantic objects** at **different altitudes**: a whole-program trace-set
refinement cannot be composed with a fragment state-transformer equation. To rewrite
`semantics_decls s «main» boundScanProg` into the Lean spec's own result requires
**whole-program Link A**, which is *not proven*:

- the scan-`While` loop's **invariant proof** (the rolling `step`/`scanFrom` digest
  vs `LoadByte` memory relation) — C1 §4-A-2, the explicitly-deferred multi-day item;
- the **FFI-trace refinement** of `@load_vec` (loads the control block + arena) and
  `@report_vec` (emits the result word).

So there is **not yet** one closed spec→machine-code theorem for the *whole*
boundScan primitive. The gap is a **front-end** refinement obligation — **not** a
backend side-condition (the backend half is closed at this program by §2) and
**not** leanc.

## 5. Honest verdict — is leanc out of the TCB end-to-end for boundScan?

**leanc (the emitter) is OUT of the TCB** — unchanged from C10 and reconfirmed here:
its text is turned into the AST by the CakeML-**verified** Pancake parser
(`boundScanProg_is_parser_output`), and nothing about leanc's translation is trusted.

**The backend half of the chain is now ONE closed kernel-checked theorem at the
concrete emitted program** (`boundScanProg_linkB`): the real
`pan_to_target_compile_semantics` instantiated at `boundScanProg`, the four
program-level side conditions **discharged against the real backend constants**,
resting only on (a) the HOL4+CakeML kernels, (b) the standard x64
machine-state-install package, (c) the backend-run `compile_prog_max` (a
computation), and (d) the single FFI-oracle spec + source non-failure. **None of
(a)–(d) is leanc.** This closes the exact `MATCH_MP` C0–C10 named as the one
build-gated pending step.

**There is NOT yet a single end-to-end spec→machine-code theorem for the whole
primitive**, and the exact remaining item is **whole-program Link A** — the scan
`While`-loop invariant + the `@load_vec`/`@report_vec` FFI-trace refinement (C1 §4-A-2,
the deferred front-end item). Concretely, "leanc fully out of the TCB for one
primitive, end to end" now stands at: **front-end emitter out (verified parser) ✓,
Link-A bounds decision proven ✓, Link-B backend closed-at-this-program ✓ (this
report), whole-program Link-A scan-loop + FFI refinement — the one open front-end
obligation ✗.** The backend, once the long pole, is no longer the blocker; the
blocker is the front-end whole-program refinement, and it is a proof obligation of
known shape, not a build or a trust hole.

Optional next hardening (not required for the above verdict): run
`compile_prog_max` on `boundScanProg` under a concrete x64 config to replace the
bound `bytes` with literal machine code (removes residual §3.3's variable), and
discharge whole-program Link A's scan-loop invariant to compose §2 with a
whole-program spec-refinement into the single end-to-end theorem.

## 6. Files (under `docs/engine/probes/compiler/hol-c11/`)

- `boundScanLinkBInstScript.sml` — the C11 theory: `boundScanProg` as parser output,
  the four side conditions discharged against the **real** backend constants, and
  `boundScanProg_linkB` (the instantiated `pan_to_target_compile_semantics`).
- `boundscan.pnk` — the exact emitted text (identical to C10's).
- `Holmakefile` — `INCLUDES` incl. `pancake/proofs`, `compiler/backend/proofs`
  (build with `CAKEMLDIR=~/src/cakeml`).
- `verify_c11.sml` / `verify_out.txt` — printed statements + program text.
- `tags_out.txt` — `[oracles: DISK_THM] [axioms: ]` on `boundScanProg_linkB`,
  `axioms "boundScanLinkBInst" = 0`.
- `build_c11.log` — green build (`boundScanLinkBInstTheory … OK`).
