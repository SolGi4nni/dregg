# C15 REPORT — the loop-free class now DESCENDS AUTOMATICALLY: a THIRD, structurally-different primitive closes its full spec→machine-code descent with **~0 lines of bespoke hand-proof**, the branch core discharged by a REUSABLE tactic and Link B produced by a GENERATOR — `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, kernel-checked, rebuilt green on hbox

**Date:** 2026-07-06 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C14 used.
**Status:** C13 closed ONE primitive's full descent (`boundScan`, bounds decision
+ scan-`While` loop) at a **629-line** loop-invariant cost. C14 closed a SECOND
(`step`, branch-only, no loop) with a **~55-line** bespoke branch core, and named
the automation path: (a) a decision **tactic** for loop-free Link-A cores, (b) a
**generator** for the whole-program wrapper + Link B. **C15 builds (a) and (b) as
reusable machinery and cranks a THIRD, deliberately different loop-free primitive
— an HTTP status-code classifier — through them with essentially NO bespoke
hand-proof.** It is **CLOSED**: `statusEndToEnd$status_machine_code`,
**`[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, kernel-checked, rebuilt
green on hbox.** The branch core is derived by **one** invocation of the reusable
`panAutoLib.panLinkA_branch` tactic; Link B by **one** call of the
`panAutoLib.mk_linkB` generator. leanc stays out of the TCB (verified parser).

---

## 1. THE third theorem (verbatim, `statusEndToEndTheory`)

```
[oracles: DISK_THM] [axioms: ]
⊢ (compile_prog_max c mc statusClassProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
   FDOM s.eshapes = FDOM (get_eids (functions statusClassProg)) ∧
   backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
   mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
   … the standard CakeML heap/bitmap/register-layout + alignment package … ∧
   s.ffi = ffi ∧ (mc.target.config.big_endian ⇔ s.be) ∧
   OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
   pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
     (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
  statusFFI code s ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (statusClass code)) F) rb])}
```

Verified: `axioms "statusEndToEnd" = 0` (and `= 0` for **all nine** C15 theories —
`statusEndToEnd, statusInstall, statusLinkBInst, statusMainRefine, statusSem,
statusWrapper, statusCore, c14Generic, panAuto`). `DISK_THM` is the benign
disk-export tag on every CakeML theory — no `cheat`, no `mk_thm`, no axiom,
identical trust footing to C11–C14.

**Reading it.** Under the standard CakeML machine-state install package (taken
**verbatim** from `statusClassProg_linkB`'s antecedent) and the single FFI-oracle
contract `statusFFI code s`, **every** observable behaviour of the installed x64
machine code is the **single** terminating trace whose reported word is **exactly**
`n2w (statusClass code)` — the Lean spec `model/StatusClass.lean` `C15.statusClass`
applied to status code `code`. `statusClass code = if code<200 then 1 else if
code<300 then 2 else if code<400 then 3 else if code<500 then 4 else 5` is
byte-identical to the Lean definition. The backend side condition
`semantics_decls s «main» statusClassProg ≠ Fail` is **proved here** from the
Link-A wrapper, not assumed.

**Why this primitive.** boundScan is *bounds-decision + scan-`While`* (loop; C13,
629-line invariant). `step` is a *2-guard/3-leaf nested `If`* (branch; C14, 55-line
core). The status classifier is a **4-guard/5-leaf LINEAR cascade** — deeper than
`step`, reading **ONE** input word (vs `step`'s two, exercising the N=1 read spine),
all-constant leaves, no loop. A fresh loop-free shape, to test whether the class
**cranks through automatically** rather than needing per-primitive proof.

## 2. What was AUTOMATIC vs what was supplied

```
   spec  ══[panLinkA_branch: REUSABLE tactic]══▶  «result» = n2w (statusClass code)
     │        ↑ ONE invocation, 0 bespoke tactic steps (§3)
   [statusWrapper statusFFI]  the load_vec/report_vec oracle CONTRACT     ← TEMPLATE (offsets/N)
     ▼
   evaluate (statusMainBody,s0)=(Return 0w,sF), trace = <spec word>       ← TEMPLATE (statusMainRefine)
     │   (c14Generic: noFFI, Seq/Dec/Annot-trace, load/store lemmas)       ← REUSABLE verbatim (1 lemma generalized)
   [statusSem  main_semantics]  all-clocks panSem$semantics lift          ← TEMPLATE (+ c14Generic semLift)
     ▼
   [statusInstall]  single-Function install → semantics_decls             ← TEMPLATE
     ▼
   [statusEndToEnd]  ∘  statusClassProg_linkB  (Link B)                   ← TEMPLATE (generic composition)
     ▲
   [statusLinkBInst]  mk_linkB GENERATOR: parse → prog, 4×EVAL, INST Link B ← AUTOMATIC (§4)
```

## 3. THE BESPOKE CORE PROOF — now ~0 lines (the headline result)

The branch core `evaluate_statusCore` — the refinement that cost boundScan **629**
lines and `step` **55** — is now discharged by **one** call of the reusable library
tactic, its **only** per-primitive inputs the three definitional theorems and the
finite guard list:

```
Theorem evaluate_statusCore:
  statusRel code r0 s ⇒
  evaluate (statusCore, s) =
    (NONE, set_var «result» (ValWord (n2w (statusClass code))) s)
Proof
  panLinkA_branch (statusRel_def, statusClass_def, statusCore_def)
    [“code < 200n”, “code < 300n”, “code < 400n”, “code < 500n”]
QED
```

`[oracles: DISK_THM] [axioms: ]`. **Zero bespoke tactic steps.** Contrast:

| primitive | shape | bespoke Link-A core proof | kind |
|---|---|---:|---|
| C13 `boundScan` | bounds + scan-`While` | **~629 lines** | synthesise + prove a loop invariant (`digInv`, `FOLDL`-digest over a `LoadByte` mem-relation) |
| C14 `step` | 2-guard/3-leaf nested `If` | **~55 lines** | hand case-split (3 leaves), reused c2 guard lemmas |
| **C15 `statusClass`** | 4-guard/5-leaf cascade | **~2 lines** (one `panLinkA_branch` call + the 4-guard list) | **library-tactic call, 0 hand steps** |

The tactic (`panAutoLib.panLinkA_branch`, 43 lines, program-agnostic) reads
`statusRel_def` to map each pinned num-var to its Pancake local, evaluates every
`Cmp Less` guard via the **generic** `panAuto$eval_lt_pinned` (no per-primitive
guard lemmas — C14 still opened c2's `eval_class_guard`/`eval_cap_guard`), and
case-splits the finite guard set leaf-by-leaf against the spec. It rests on the
program-agnostic theory `panAutoScript.sml` (`signed_lt_n2w64`, `eval_lt_pinned`,
`evaluate_If_reduce`, `cond1w_ne0`, `evaluate_Assign_const`, `Annot_Seq_eval`),
built once.

## 4. Link B — produced by the mk_linkB GENERATOR

`statusLinkBInstScript.sml` is **35 lines**, and the substance is a **single**
generator call:

```
val linkB_result = mk_linkB { pnkFile = "statusclass.pnk", progName = "statusClassProg" };
```

`panAutoLib.mk_linkB` (program-agnostic, 48 lines) parses the `.pnk` with the
**verified** parser (`statusClassProg_is_parser_output`, `[oracles: DISK_THM]
[axioms: ]` — leanc OUT of the TCB), binds the program constant, discharges the
four EVAL side conditions (`pancake_good_code`, `distinct_params`,
`distinct_names`, `size_of_eids < dimword(:64)`) against the **real** backend
constants, and specializes `pan_to_target_compile_semantics` at the program. The
**only** per-primitive inputs are the `.pnk` filename and the program name. (Fix
made this pass: the generator refers to the freshly-defined program constant **by
name**, not by antiquoting the polymorphic AST term — the latter yields "No
consistent parse".)

## 5. THE RESIDUAL PER-PRIMITIVE WORK — what a NEW loop-free primitive still costs

Bespoke **proof** ≈ **0**. What remains is **declarations/data + template
parameterization**, no new tactic engineering:

1. **The `.pnk`** (the implementation) and **the Lean spec re-declared in HOL**
   (`statusClass_def`, 8 lines) — irreducible inputs.
2. **`statusCore_def`** (~15 lines): the verbatim emitted `If` cascade. Mechanically
   dumpable from the verified parser output (we confirmed it against the AST dump);
   not hand-invented.
3. **`statusRel_def`** (~6 lines): the input/output relation + the range bound the
   signed guards need.
4. **The guard-predicate list** passed to `panLinkA_branch` (4 terms). Auto-derivable
   from the `Cmp Less` nodes of `statusCore_def` — currently supplied by hand.
5. **The control-block layout** in the wrapper: `statusCtrlStaged`/`statusFFI`
   (input offsets, N reads, result-slot offset). One FFI-oracle contract, the single
   named trusted assumption.
6. **The wrapper template edits** (`statusMainRefine` + `statusSem`/`statusInstall`/
   `statusEndToEnd`): the read-count **N** (number of `Dec`-read layers — here 1 vs
   `step`'s 2) and the store/report **offset** (+8w vs `step`'s +24w). Sub-term
   extraction is **automatic** — the forward wrap `rand`-walks the emitted body and
   discharges each `Dec`/`Annot`/`Seq` node with the uniform `decw`/`annotw`/`seqldw`
   tactics, so **no annotation string is hand-transcribed**. Only one generic lemma
   changed: `c14Generic$evaluate_store_result` was **generalized** from a fixed +24w
   to an arbitrary offset parameter (strict generalization, proof unchanged).

**Line comparison (per-span, spec→machine-code):** C15's nine scripts total
**~1075 lines**, of which **~464 (43%) are 100% program-agnostic REUSABLE** —
`panAuto` (124) + `panAutoLib` (125) + `c14Generic` (215) — carried with **zero**
new proof and closing for **any** loop-free load_vec/report_vec program. The rest
is TEMPLATE (~540, only offsets/N/spec-word edited) + declarations. The genuinely
**bespoke proof residual is 0** (the `evaluate_statusCore` `Proof` is a library
call). Compare the same span: C13 ≈ 1751, C14 ≈ 895.

## 6. THE HONEST REMAINING AUTOMATION GAP

The **core** (the expensive, mathematically-substantive part) is fully automatic
via the tactic; **Link B** is fully automatic via the generator. What is **not yet
a single mechanical generator** is the **whole-program wrapper**
(`statusMainRefine`/`Sem`/`Install`/`EndToEnd`): it is a fixed **template** that
still needs two per-primitive parameters edited — the read-count **N** and the
store/report **offset**. This is **not new proof** (no obligation is discharged by
hand; the skeleton and every tactic are reused), but it is not yet a `mk_wrapper`
function analogous to `mk_linkB`. Closing this gap is a **fold over the `Dec`-read
spine** of arbitrary length N, reading the offsets off the emitted `Store`/`ExtCall`
nodes — mechanical ML, no metatheory. Two primitives (`step` N=2/+24w, `statusClass`
N=1/+8w) now pin down exactly what that fold must abstract. **Loops remain
hand-proved** (invariant synthesis), with the `FOLDL`-over-array sub-class as the
semi-automatable middle — unchanged from C14 §4.3.

## 7. Trust ledger (unchanged from C13/C14; none of it is leanc)

1. **HOL4 + CakeML kernels.** Every C15 theory is `[oracles: DISK_THM] [axioms: ]`,
   0 cheats (`axioms = 0` for all nine). `statusClass` is byte-identical to
   `model/StatusClass.lean`.
2. **The standard CakeML machine-state install package** — taken **verbatim** from
   `statusClassProg_linkB`'s antecedent; the backend correctness consuming it is
   C11's fully-built `pan_to_target_compile_semantics`.
3. **The single FFI-oracle contract `statusFFI`** — `@load_vec` stages the one
   control word `code`; `@report_vec` emits the result word onto the trace. The one
   irreducible honest assumption, structurally identical to `step`'s, simpler
   (one input word, no arena).

**leanc is OUT of the TCB** — `statusClassProg` is the verified parser's output on
the emitted bytes (`statusClassProg_is_parser_output`).

## 8. Verdict

- **Does a 3rd loop-free primitive now descend AUTOMATICALLY, spec→machine-code?**
  **Yes.** `statusEndToEnd$status_machine_code`, `[oracles: DISK_THM] [axioms: ]`,
  0 axioms, 0 cheats, rebuilt green on hbox: the installed x64 machine code emitted
  for the status classifier can only ever report the exact Lean spec word
  `n2w (statusClass code)`, under the standard install package + the single
  FFI-oracle contract.
- **Bespoke hand-proof for the branch core:** **~0 lines** — one `panLinkA_branch`
  library-tactic call (vs boundScan **629**, step **55**). The core collapsed from
  *hand-cased leaves* (C14) to *a single reusable tactic invocation* (C15).
- **Link B:** produced by the `mk_linkB` generator (one call, `.pnk` + name).
- **Residual per-primitive work:** the spec + relation + verbatim core-`Def` +
  control-block layout + two wrapper parameters (read-count N, result offset). No
  new proof. The one remaining automation gap — turning the wrapper template into a
  `mk_wrapper` fold over the N-read spine — is mechanical ML, precisely scoped by
  two worked primitives (N=1 and N=2).
- **Does the loop-free class SCALE?** **Yes** — a third, structurally-different
  primitive closed its full descent with the expensive part (the core) fully
  automatic and Link B fully automatic. The class **cranks through**; the only
  hand-labour left is data (declarations) and a two-parameter template edit.

## 9. Files (`docs/engine/probes/compiler/hol-c15/`, built on hbox `~/hol-c15b`)

- `statusclass.pnk` — the emitted status classifier (leanc's artifact; verified
  parser's input).
- `panAutoScript.sml` — **REUSABLE program-agnostic THEORY** (`signed_lt_n2w64`,
  `eval_lt_pinned`, `evaluate_If_reduce`, `cond1w_ne0`, `evaluate_Assign_const`,
  `Annot_Seq_eval`) the tactic rests on. Built once.
- `panAutoLib.sml` — **THE REUSABLE AUTOMATION (ML)**: `panLinkA_branch` (loop-free
  Link-A decision tactic) + `mk_linkB` (whole-program Link-B generator).
- `c14GenericScript.sml` — program-agnostic descent machinery (noFFI, Seq/Dec/Annot
  -trace, load/store lemmas, semLift); byte-identical to C14 **except**
  `evaluate_store_result` generalized to an arbitrary result-slot offset.
- `statusCoreScript.sml` — spec `statusClass_def`, verbatim core `statusCore_def`,
  relation `statusRel_def`, and `evaluate_statusCore` **derived by the library
  tactic** (0 bespoke steps).
- `statusLinkBInstScript.sml` — Link B via **one `mk_linkB` call** (35 lines).
- `statusWrapperScript.sml` — `statusCtrlStaged`/`statusFFI` (1 input word, +8w
  result slot) + `statusMainBody` built by ML surgery from `functions
  statusClassProg`.
- `statusMainRefineScript.sml` — the whole-`main` FFI-trace wrapper (N=1 read,
  +8w store/report), template adapted from C14, sub-terms extracted by ML `rand`-walk.
- `statusSemScript.sml` / `statusInstallScript.sml` / `statusEndToEndScript.sml` —
  clock-lift, single-Function install, and **the final composition
  `status_machine_code`**.
- `Holmakefile` — INCLUDES the CakeML pancake/backend/proofs dirs; build with
  `CAKEMLDIR=~/src/cakeml`. **No `~/c2` dependency** — C15 is
  machine-step-independent (the generic tactic replaced c2's guard lemmas).
