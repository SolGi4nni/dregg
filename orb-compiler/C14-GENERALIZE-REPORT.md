# C14 REPORT — the descent GENERALIZES: a SECOND, structurally-different primitive now has ONE closed spec→machine-code theorem, `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats — plus the quantified reusable-vs-bespoke split and the concrete automation roadmap to the generic front-end

**Date:** 2026-07-06 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 `a9846ebe2` (Trindemossen 2, stdknl), CakeML `ed31510b3`** — the exact
tree C1–C13 used. **Status:** C13 closed ONE primitive's full descent
(`boundScan`, a bounds decision + a scan-`While` digest loop). C14 cranks a
SECOND, deliberately **structurally-different** primitive — a **branch-only**
machine step (a nested decision, **NO loop**) — through the identical chain:
spec → leanc-emitted Pancake → CakeML-verified parser → Link A → C11-style
backend Link B → `machine_sem ⊆ { spec output }`. It is **CLOSED**:
`stepEndToEnd$step_machine_code`, **`[oracles: DISK_THM] [axioms: ]`, 0 axioms,
0 cheats, kernel-checked, rebuilt green on hbox.** leanc is out of the TCB
(verified parser). The descent is not a one-off: the backend half and the
whole-program wrapper were **reused**, and the only genuinely new hand-proof
was the branch core — which is **decidable**, not a loop invariant.

---

## 1. THE second theorem (verbatim, `stepEndToEndTheory`)

```
⊢ (compile_prog_max c mc stepGateProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
   FDOM s.eshapes = FDOM (get_eids (functions stepGateProg)) ∧
   backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
   mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
   … the standard CakeML heap/bitmap/register-layout + alignment package … ∧
   s.ffi = ffi ∧ (mc.target.config.big_endian ⇔ s.be) ∧
   OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
   pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
     (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
  stepFFI c b s ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (mstep c b)) F) rb])}
```

`[oracles: DISK_THM] [axioms: ]` (verified: `axioms "stepEndToEnd" = 0`;
`DISK_THM` is the benign disk-export tag on every CakeML theory — no `cheat`,
no `mk_thm`, no axiom, identical trust footing to C11/C12/C13).

**Reading it.** Under the standard CakeML machine-state install package (the
first bracketed conjunction — taken **verbatim** from `stepGateProg_linkB`'s
antecedent) and the single FFI-oracle contract `stepFFI c b s`, **every**
observable behaviour of the installed x64 machine code is the **single**
terminating trace whose reported word is **exactly** `n2w (mstep c b)` — the
Lean spec `model/MachineStep.lean` `C2.step` applied to counter `c` and byte
`b`. `mstep c b = if b < 128 then c else if c < 255 then c + 1 else 255` is
byte-identical to `C2.step` (both agree on the reachable domain `c ≤ 255`,
`b < 256`, exactly per C2-MACHINE-REPORT's faithfulness note). The backend side
condition `semantics_decls s «main» stepGateProg ≠ Fail` is **proved here** from
the Link-A wrapper, not assumed.

**Why this primitive.** boundScan's shape is *bounds-decision + scan-`While`
loop*; its closed descent (C13) cost a **629-line loop-invariant** (C12's
`digInv` + induction). The machine step's shape is a *nested `If`, no loop* —
the branch-only case the task named as the first automatable sub-case. Proving
it end-to-end demonstrates (a) the chain is not boundScan-specific, and (b) the
per-primitive cost collapses when the loop is gone.

## 2. The closed chain (what was REUSED vs what was NEW)

```
   spec  ══[stepCore: branch case-split]══▶  «result» = n2w (mstep c b)     ← BESPOKE (but DECIDABLE)
     │                                                                        (reuses c2 guard lemmas)
   [stepWrapper stepFFI]  the load_vec/report_vec oracle CONTRACT             ← TEMPLATE (shape = boundScanFFI)
     ▼
   evaluate (stepMainBody,s0)=(Return 0w,sF), trace = <spec word>            ← TEMPLATE (stepMainRefine)
     │   (c14Generic: noFFI, Seq/Dec/Annot-trace, load/store lemmas)          ← REUSABLE verbatim (C13 generic)
   [stepSem  main_semantics]  all-clocks panSem$semantics lift               ← TEMPLATE  (+ c14Generic semLift)
     ▼
   [stepInstall]  single-Function install → semantics_decls                  ← TEMPLATE
     ▼
   [stepEndToEnd]  ∘  stepGateProg_linkB  (Link B)                           ← TEMPLATE (generic composition)
     ▲
   [stepLinkBInst]  parser → stepGateProg, EVAL side-conds, INST backend     ← NEAR-AUTOMATIC (C11 procedure)
```

## 3. THE SPLIT — reusable vs bespoke, quantified

C14's eight proof scripts total **895 lines** (vs C13+C12+C11's ≈ **1751** for
the same span of boundScan: 629 core + 934 wrapper/sem/install/e2e + 109 Link B
+ 64 semLift + generic). Per file, categorized, with the C13/C11 counterpart:

| C14 file | lines | category | C-counterpart | genuinely EDITED |
|---|---:|---|---:|---:|
| `c14GenericScript.sml` | 213 | **REUSABLE (program-agnostic)** | C13 semLift 64 + generic 149 | **0** (byte-identical) |
| c2 `machineStepLinkA` (opened) | ~68 | **REUSABLE** (`mstep`,`mstep_le`,`signed_lt_n2w64`,`eval_class_guard`,`eval_cap_guard`) | — | **0** (reused via `open`) |
| `stepLinkBInstScript.sml` | 79 | **NEAR-AUTOMATIC** (parse+4×EVAL+1×SIMP) | C11 109 | ~6 (`.pnk`+prog name) |
| `stepWrapperScript.sml` | 76 | TEMPLATE (FFI shape + mainBody surgery) | C13 wrapper 412* | ~15 (ctrlStaged content) |
| `stepMainRefineScript.sml` | 206 | TEMPLATE (load→read→core→store→report→return) | C13 238 | ~20 (2 reads not 3; no clock hyp) |
| `stepSemScript.sml` | 75 | TEMPLATE | C13 87 | ~8 (dropped clock-budget) |
| `stepInstallScript.sml` | 55 | TEMPLATE | C13 59 | ~5 |
| `stepEndToEndScript.sml` | 59 | TEMPLATE (generic ML composition) | C13 88 | ~4 |
| `stepCoreScript.sml` | 132 | **BESPOKE** (branch case-split) | C12 core 629 | ~55 (new proof) |

\* C13's 412-line `boundScanWrapper` bundled the generic lemmas **with**
boundScan-specific defs; C14 split the generic half into `c14Generic` (reused)
and kept only the per-primitive FFI/mainBody (76).

**Bottom line of the split:**

- **~281 lines (31%) are 100% REUSABLE program-agnostic machinery** — `c14Generic`
  (213) + the opened c2 guard lemmas (~68) — carried across boundScan→step with
  **zero** new proof. These close for **any** load_vec/report_vec Pancake program.
- **~550 lines (61%) are TEMPLATE** — the whole-program wrapper + Link B. The
  skeleton is fixed; only **~60 lines total** were genuinely edited (program name,
  `.pnk` bytes, the control-block layout `stepCtrlStaged`, the "2 reads vs 3"
  spine, the spec-word function `n2w (mstep c b)`, and dropping the loop's clock
  hypotheses). Link B specifically is **near-automatic**: `parse_topdecs_to_ast`
  + four `EVAL` side-conditions + one `SIMP_RULE` — identical procedure for both
  primitives, built green in 14 s.
- **~55 lines (6%) are genuinely BESPOKE per-primitive hand-proof** — the branch
  core `evaluate_stepCore` (three leaf case-splits). This is the **only** place
  new mathematics entered, and it **shrank ~11×** vs boundScan (55 vs 629) **and
  changed kind**: from *synthesize-and-prove a loop invariant* to *case-split on
  finitely many guards*.

The single trusted assumption is unchanged and named: the **FFI-oracle contract**
`stepFFI` (the `@load_vec`/`@report_vec` observable trace), structurally identical
to `boundScanFFI` (only `stepCtrlStaged` — two control words, **no arena
`memRel`** — differs). leanc stays OUT: `stepGateProg` is the CakeML-**verified**
parser's output on `machinestep_gate.pnk`'s exact bytes
(`stepGateProg_is_parser_output`, `[oracles: DISK_THM] [axioms: ]`).

## 4. THE AUTOMATION PATH — decidable sub-case named, boundary drawn honestly

The evidence from two primitives isolates **exactly** where automation is
reachable and where it is not:

### 4.1 The per-primitive Link-A core: DECIDABLE for loop-free bodies (do this first)

`evaluate_stepCore` is the whole bespoke residual, and its proof is
`Cases_on` on each `If` guard + `simp`. For a Pancake function body built from
`Dec/Assign/If/Store/Load/ExtCall` with **no `While`**, `panSem$evaluate` is a
**terminating structural recursion that consumes no clock** — so the refinement

  `evaluate (body, s) = (NONE, set_var result (ValWord (spec …)) s)`

is decidable by **symbolic execution + finite guard case-split**: there are
exactly *k* leaves, where *k* = the number of `If`-nesting paths (here 3), always
finite for a loop-free body. This is a **translation-validation** decision
procedure (per-program, automatic): a tactic `panLinkA_branch` that (i) symbolic-
ally evaluates the body, (ii) splits on each guard via the target semantics of
`Cmp`, (iii) checks each straight-line leaf against the spec's corresponding
branch. `evaluate_stepCore` **is** that procedure, run by hand; mechanizing it is
tactic engineering, not new metatheory. **First automatable sub-case: every
loop-free (straight-line + branch) primitive** — decision fragments, header-field
lookups, fixed-width encoders, saturating/clamping arithmetic, route-match cores
that fan out to a bounded switch. The machine step is the worked instance.

### 4.2 The whole-program wrapper + Link B: a GENERATOR (mechanical, not decidable)

The wrapper (`stepMainRefine`/`stepSem`/`stepInstall`/`stepEndToEnd`) is a
**fixed template parameterized by** ⟨control-word list, the core Link-A theorem,
the spec-word term⟩. The bottom-up forward wrap in `stepMainRefine` **already** is
a generator skeleton: it extracts the emitted `Dec/Annot/Seq` spine in ML by
`rand`-walking `stepMainBody` and discharges each node with a uniform
`decw`/`annotw`/`seqldw` tactic. Generalising from *N=2* reads to arbitrary *N* is
a fold over the `Dec` spine — no new proof obligation. Link B is likewise a
program-agnostic instantiation of `pan_to_target_compile_semantics` (four `EVAL`
side-conditions that hold for any well-formed program). So the wrapper + backend
half is a **whole-program proof generator**: feed it the parsed program and the
§4.1 core theorem, it emits the closed `machine_code` theorem. Building this
generator turns "loop-free primitive → closed descent" **fully automatic**.

### 4.3 What STAYS hand-proved — the honest boundary: loops

A `While` loop needs a **loop invariant** (boundScan's `digInv`: the rolling
`acc = FOLDL step init (TAKE i buf)` digest tied to a `LoadByte` memory
relation). The invariant encodes the fold's mathematical meaning; **synthesising
it is not decidable in general** — this is the genuine boundary, and it is why
the loop core cost 629 lines while the branch core cost 55.

Two honest gradations inside "loops":
- **Templatable loop class** (semi-automatable): a *bounded fold over an array
  with a rolling accumulator* has the schema invariant
  `acc_i = FOLDL step init (TAKE i buf) ∧ i ≤ len`, instantiable per
  ⟨`step`, `init`⟩. boundScan's `digInv` is one instance; the parseline SP-scans
  (C6) are another. For this class the invariant is a **schema fill-in**, not a
  synthesis — mechanizable with a per-`step` obligation.
- **General loops** (hand-proved): data-dependent termination, nested loops,
  loops whose invariant is not a fold-over-input — these need a human-supplied
  invariant. This is the standing research boundary (invariant synthesis), and
  the report does not claim to cross it.

### 4.4 Roadmap to the generic front-end

1. **Now closed twice:** Link B is near-automatic for any program (boundScan,
   step — identical procedure). ✓
2. **Immediately buildable:** the §4.1 `panLinkA_branch` decision tactic + the
   §4.2 wrapper generator ⇒ **every loop-free primitive closes its full descent
   automatically**. The machine step proves the target shape is reachable.
3. **Next:** the §4.3 templatable-loop schema (`FOLDL`-over-array) ⇒ a large,
   common loop class (scans, digests, checksums, header walks) becomes a
   per-`step` fill-in.
4. **Boundary:** arbitrary loops stay hand-proved (invariant synthesis, open).

So the generic front-end is **not** "one theorem for the whole spec at once"; it
is a **classifier + two generators**: loop-free → fully automatic; fold-loops →
schema-instantiated; general loops → hand-proved. C14 closes item (1)–(2)'s
worked instance end-to-end and names (3)–(4) precisely.

## 5. Trust ledger (unchanged from C13; none of it is leanc)

1. **HOL4 + CakeML kernels.** Every C14 theory is `[oracles: DISK_THM]
   [axioms: ]`, 0 cheats (`axioms "step…" = 0` for all seven theories). `mstep`
   is byte-identical to `model/MachineStep.lean` `C2.step`.
2. **The standard CakeML machine-state install package** — taken **verbatim**
   (antiquoted) from `stepGateProg_linkB`'s antecedent; the backend correctness
   consuming it is C11's fully-built `pan_to_target_compile_semantics`.
3. **The single FFI-oracle contract `stepFFI`** — `@load_vec` stages the two
   control words `c`/`b`; `@report_vec` emits the result word onto the trace. The
   one irreducible honest assumption (the observable behaviour *is* an FFI trace),
   structurally identical to boundScan's, **simpler** (no arena).

**leanc is OUT of the TCB** — `stepGateProg` is the verified parser's output on
the emitted bytes; the emitter is validated, not trusted.

## 6. Verdict

- **Does a 2nd primitive now have a closed spec→machine-code descent?** **Yes.**
  `stepEndToEnd$step_machine_code`, `[oracles: DISK_THM] [axioms: ]`, 0 axioms,
  0 cheats, rebuilt green on hbox: the installed x64 machine code emitted for the
  machine step can only ever report the exact Lean spec word `n2w (mstep c b)`,
  under the standard install package + the single FFI-oracle contract. The
  descent **generalizes**.
- **The reusable-vs-bespoke split (quantified):** ~31% program-agnostic REUSABLE
  (0 new proof), ~61% TEMPLATE (~60 edited lines, Link B near-automatic), ~6%
  genuinely BESPOKE — and that bespoke core **shrank ~11×** (55 vs 629 lines)
  **and changed kind** (branch case-split, not loop invariant) going from
  boundScan to the branch-only step.
- **The automation path:** the loop-free Link-A core is **decidable**
  (translation-validation, tactic-mechanizable — the first automatable sub-case,
  worked here); the whole-program wrapper + Link B is a **fixed generator**
  (near-automatic, demonstrated twice); **loops stay hand-proved** (invariant
  synthesis), with a **templatable fold-over-array sub-class** as the semi-
  automatable middle. The generic front-end is a classifier + two generators, not
  a single monolith — and C14 closes the loop-free instance end-to-end.

## 7. Files (`docs/engine/probes/compiler/hol-c14/`, built on hbox `~/hol-c14`)

- `machinestep_gate.pnk` — the emitted branch-only step (leanc's artifact; the
  verified parser's input).
- `c14GenericScript.sml` — the **program-agnostic** descent machinery (noFFI,
  Seq/Dec/Annot-trace, control-block load/store lemmas, `semantics_Return_lift`);
  byte-identical to C13's generic lemmas + semLift (re-declared to sidestep a
  cross-tree theory-hash clash between `~/c2`'s and `~/c6work`'s `machineStepLinkA`).
- `stepCoreScript.sml` — **the bespoke branch core**: `stepCore` (verbatim
  emitted `If`), `stepRel`, `evaluate_stepCore` (= `n2w (mstep c b)` into
  «result», by case-split), framed + `noFFI`; reuses c2 `machineStepLinkA`
  guards.
- `stepLinkBInstScript.sml` — **Link B**, near-automatic: parser output
  `stepGateProg`, four EVAL side-conditions, instantiated
  `pan_to_target_compile_semantics`.
- `stepWrapperScript.sml` — `stepCtrlStaged` (2 words, no arena), the FFI-oracle
  contract `stepFFI`, and `stepMainBody` **built by ML surgery** from
  `functions stepGateProg` (no hand transcription — the parser output modulo the
  `stepCore` abbreviation).
- `stepMainRefineScript.sml` — the whole-`main` FFI-trace wrapper
  (`stepMainBody_refines`), adapted from C13's template.
- `stepSemScript.sml` — `call_main_run`, `main_semantics` (any nonzero clock;
  no loop budget).
- `stepInstallScript.sml` — `stepGateProg_semantics_decls` (single-Function
  install + decls-level Link A).
- `stepEndToEndScript.sml` — **THE** final composition `step_machine_code`.
- `verifyScript.sml` / `verify_out.txt` — printed statements + tags +
  `axioms = 0` for all seven theories.
- `Holmakefile` — `INCLUDES` the CakeML pancake/backend/proofs dirs + `~/c2`
  (`machineStepLinkA`); build with `CAKEMLDIR=~/src/cakeml`.
