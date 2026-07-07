# C13 REPORT — CLOSED: ONE kernel-checked spec→machine-code theorem for boundScan

**Date:** 2026-07-06 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 `Trindemossen 2` (stdknl), CakeML `ed31510b3`** — the exact tree C1–C12
used. **Status:** the residual named in C12 §3/§5 — the FFI-trace wrapper + the
`semantics_decls` clock-lift + the whole-program install + the Link-B
composition — is now **discharged**. There is **ONE closed spec→machine-code
theorem** for boundScan: `boundScanEndToEnd$boundScan_machine_code`,
**`[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, kernel-checked.**

---

## 1. THE theorem (verbatim, `boundScanEndToEndTheory`)

```
⊢ (compile_prog_max c mc boundScanProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
   FDOM s.eshapes = FDOM (get_eids (functions boundScanProg)) ∧
   backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
   mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
   0w <₊ mc.target.get_reg ms mc.len_reg ∧
   globals_size = (let dec_shs = dec_shapes boundScanProg;
                       struct_ctxt = decs_stcnames [] boundScanProg
                   in SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) ∧
   mc.target.get_reg ms mc.len_reg <₊ mc.target.get_reg ms mc.ptr2_reg ∧
   mc.target.get_reg ms mc.len_reg = s.base_addr ∧
   globals_allocatable s boundScanProg ∧
   heap_len = w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * s.base_addr) DIV
                  (dimindex (:64) DIV 8) ∧
   s.top_addr = s.base_addr + bytes_in_word * n2w heap_len −
                n2w (globals_size * dimindex (:64) DIV 8) ∧ globals_size ≤ heap_len ∧
   s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len − globals_size) ∧
   aligned (shift (:64) + 1)
     (mc.target.get_reg ms mc.ptr2_reg + -1w * mc.target.get_reg ms mc.len_reg) ∧
   adj_ptr2 = mc.target.get_reg ms mc.len_reg + bytes_in_word * n2w max_stack_alloc ∧
   adj_ptr4 = mc.target.get_reg ms mc.len2_reg − bytes_in_word * n2w max_stack_alloc ∧
   adj_ptr2 ≤₊ mc.target.get_reg ms mc.ptr2_reg ∧
   mc.target.get_reg ms mc.ptr2_reg ≤₊ adj_ptr4 ∧
   w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * mc.target.get_reg ms mc.len_reg) ≤
     w2n bytes_in_word * (2 * max_heap_limit (:64) c.data_conf − 1) ∧
   w2n bytes_in_word * (2 * max_heap_limit (:64) c.data_conf − 1) < dimword (:64) ∧
   s.ffi = ffi ∧ (mc.target.config.big_endian ⇔ s.be) ∧
   OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
   pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
     (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
  boundScanFFI a off len s ∧ (∃K. 0 < K ∧ len < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (c0_encode (boundScan a off len))) F) rb])}
```

`[oracles: DISK_THM] [axioms: ]` (verified: `axioms "boundScanEndToEnd" = 0`; the
`DISK_THM` oracle is the benign disk-export tag on every CakeML theory — no
`cheat`, no `mk_thm`, no axiom, per C11/C12).

**Reading it.** Under the standard CakeML machine-state install package (the
first bracketed conjunction — verbatim the antecedent of C11's
`boundScanProg_linkB`, i.e. the backend compiler run `compile_prog_max`, the
`pan_installed` memory image, and the register/heap layout side conditions), the
single FFI-oracle contract `boundScanFFI a off len s`, and a witness clock,
**EVERY** observable behaviour of the installed x64 machine code is the **single**
terminating trace whose reported result word is **exactly**
`n2w (c0_encode (boundScan a off len))` — the Lean spec `model/BoundScan.lean`
`C0.encode (C0.boundScan a off len)`. (`boundScan`/`c0_encode` are byte-identical
to the Lean spec and to hol-c1; established in C12.)

Note the backend side condition `semantics_decls s «main» boundScanProg ≠ Fail`
is **PROVED here** from the Link-A wrapper (the semantics is `Terminate Success`),
**not assumed** — it is filtered out of the install-package hypotheses.

## 2. How C13 closes it (composition)

```
   spec  ══[C12 evaluate_innerCore]══▶  «result» = spec word          (decision+digest core)
     │
   [C13 boundScanWrapperLinkA]  Store/@report_vec/@load_vec staging, the FFI-oracle CONTRACT
     ▼
   evaluate (mainBody, s0) = (Return 0w, sF),  sF.ffi.io_events = <trace(spec word)>   (mainBody_refines)
     │
   [C13 semLift + boundScanSem]  all-clocks panSem$semantics lift (clock monotonicity)
     ▼
   semantics s' «main» = Terminate Success <trace(spec word)>          (main_semantics)
     │
   [C13 boundScanInstall]  trivial single-Function install of boundScanProg (EVAL)
     ▼
   semantics_decls s «main» boundScanProg = Terminate Success <trace(spec word)>   (boundScanProg_semantics_decls)
     │
   [C13 boundScanEndToEnd]  ∘  C11 boundScanProg_linkB  (machine_sem ⊆ {semantics_decls …})
     ▼
   machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {Terminate Success <trace(spec word)>}
```

The two C13 stones added on top of C12:

- **`boundScanProg_semantics_decls`** (`boundScanInstallTheory`,
  `[oracles: DISK_THM] [axioms: ]`): the whole-program Link A at the **decls**
  level. `boundScanProg` is a single `Function «main»` (params `[]`, empty struct
  context), so `decs_stcnames [] boundScanProg = SOME []` and
  `evaluate_decls (s with structs := []) boundScanProg` installs
  `«main» ↦ ([], mainBody)` (both by EVAL; `mainBody` is byte-identical to the
  emitted body with the C12 `innerCore` constant in place). Composed with
  `main_semantics` and the observation that `boundScanFFI` depends on the state
  only through `base_addr`, this yields the spec-word trace for the observational
  `semantics_decls`.
- **`boundScan_machine_code`** (`boundScanEndToEndTheory`): the final MATCH_MP of
  C11's `boundScanProg_linkB` (Link B: `machine_sem ⊆ {semantics_decls …}`) with
  the above, substituting the proven `semantics_decls` value into the singleton
  set. The install-package antecedent is taken **verbatim** from
  `boundScanProg_linkB` (antiquoted, not re-transcribed), so the standard CakeML
  package is neither weakened nor drifted.

All prior C13 stones (`semLift`, `boundScanWrapperLinkA` — the FFI-oracle contract
`boundScanFFI` + `mainBody` + the Store/report/Load bridges, `boundScanMainRefine`
— the whole-`main` `mainBody_refines`, `boundScanSem` — `main_semantics`) are
kernel-checked, `[oracles: DISK_THM] [axioms: ]`.

## 3. Trust ledger (what is trusted; none of it is leanc)

1. **HOL4 + CakeML kernels.** Every C13 theorem is `[oracles: DISK_THM]
   [axioms: ]`, 0 cheats. The `boundScan`/`c0_encode` HOL definitions are
   byte-identical to `model/BoundScan.lean`.
2. **The standard CakeML machine-state install package** — the first bracketed
   conjunction of §1, verbatim `boundScanProg_linkB`'s antecedent: the backend
   compiler run `compile_prog_max c mc boundScanProg`, the `pan_installed` memory
   image, and the x64 register/heap-layout side conditions. These are the
   caller-supplied loader facts, not proof holes; the backend correctness that
   consumes them is C11's fully-built `pan_to_target_compile_semantics`.
3. **The single FFI-oracle contract `boundScanFFI`** (`boundScanWrapperLinkA`):
   `@load_vec` stages the control block + arena into memory (per `ctrlStaged`);
   `@report_vec` emits the result word onto the observable FFI trace. This is the
   one irreducible honest assumption — the observable behaviour of a boundScan run
   *is* an FFI I/O trace, so the oracle's effect is a contract, not a theorem.

**leanc is OUT of the TCB.** `boundScanProg` is the CakeML-**verified** Pancake
parser's output on leanc's exact `boundscan.pnk` bytes
(`boundScanProg_is_parser_output`, C10/C11) — the emitter is validated, not
trusted. Nothing in the residual was the backend (C11, closed) or leanc.

| Piece | Status |
|---|---|
| Emitter (leanc) out of TCB — verified parser | ✓ (C10/C11) |
| Link-A bounds decision + scan-`While` digest loop + whole core → `«result»` | ✓ (C1/C12) |
| Link-A FFI-trace wrapper (`mainBody_refines`) | ✓ (C13 `boundScanMainRefine`) |
| `semantics` all-clocks lift (`main_semantics`) | ✓ (C13 `semLift`/`boundScanSem`) |
| Whole-program install → `semantics_decls` | ✓ (C13 `boundScanInstall`) |
| Link-B backend, closed at the concrete program | ✓ (C11) |
| **spec → machine code, ONE theorem** | **✓ (C13 `boundScanEndToEnd`)** |

## 4. Verdict

**Is there now ONE closed spec→machine-code theorem for boundScan?** **Yes.**
`boundScanEndToEnd$boundScan_machine_code`, `[oracles: DISK_THM] [axioms: ]`,
0 axioms, 0 cheats, kernel-checked, rebuilt green on hbox. It states that the
installed x64 machine code emitted for boundScan can only ever report the exact
Lean spec word `C0.encode (C0.boundScan a off len)`, under the standard CakeML
install package + the single FFI-oracle contract — not leanc, not the backend.

## 5. Files (`docs/engine/probes/compiler/hol-c13/`, built on hbox `~/hol-c13`)

- `semLiftScript.sml` — `semantics_Return_lift`: the program-agnostic all-clocks
  `panSem$semantics` lift (clock monotonicity).
- `boundScanWrapperLinkAScript.sml` — the FFI-oracle contract `boundScanFFI`,
  `mainBody` (verbatim emitted body with `innerCore`), `evaluate_innerCore_framed`
  (C12 core + locals frame), and the Store/report/Load bridge lemmas.
- `boundScanMainRefineScript.sml` — `mainBody_refines`: the whole-`main` FFI-trace
  wrapper (Decs/@load_vec/Loads/core/Store/@report_vec/Return) → the spec-word trace.
- `boundScanSemScript.sml` — `call_main_run`, `main_semantics`: through the
  whole-program `Call NONE «main» []` and the semantics lift.
- `boundScanInstallScript.sml` — `boundScanProg_semantics_decls`: the trivial
  single-Function install + the decls-level Link A.
- `boundScanEndToEndScript.sml` — `boundScan_machine_code`: **THE** final
  composition with C11 `boundScanProg_linkB`.
- `verifyScript.sml` / `verify_out.txt` — printed statements + `axioms = 0` +
  `oracles = [DISK_THM], axioms = []` for both `boundScanProg_semantics_decls` and
  `boundScan_machine_code`.
- `Holmakefile` — `INCLUDES` the CakeML pancake/backend/proofs dirs + `~/c6work`
  (C3/C5/C6 loop machinery) + `~/hol-c11` (`boundScanProg`, `boundScanProg_linkB`)
  + `~/hol-c12` (`innerCore`, `digLoop`); build with `CAKEMLDIR=~/src/cakeml`.
