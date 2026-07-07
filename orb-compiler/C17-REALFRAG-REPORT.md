# C17 REPORT — the loop-free descent AUTOMATION reaches the DEPLOYED SERVE: a REAL fragment of the drorb orb (`Redirect.Code.status`, the RFC 9110 §15.4 redirect-status pick, in `deployStagesFull2`) closes its full spec→machine-code descent with a **2-line** bespoke core proof — `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, kernel-checked, green on hbox

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C15 used.
**Dir:** `docs/engine/probes/compiler/hol-c17/` (built on hbox `~/hol-c17`, all 8 theories `OK`).

---

## 0. What this probe answers

C15 automated the loop-free descent class on **TOY** primitives
(`boundScan`/`step`/`statusClass` — the last a re-declared *probe* spec in
`docs/.../model/StatusClass.lean`). The open question was the honest one: **does
the front-end reach the actual deployed serve?** C17 takes a **REAL, deployed**
drorb fragment and cranks it through the SAME machinery. It closes. The single
piece of real-serve-specific friction — algebraic-type (`enum`) dispatch lowers
to **equality** guards, not C15's ordered `<` — is named, and closed by a small
program-agnostic extension that is now reusable for every future `match`-shaped
fragment.

## 1. THE fragment — real, deployed, genuinely loop-free

**`Redirect.Code.status`** in `orb/Redirect.lean`:

```lean
def Code.status : Code → Nat
  | .moved301 => 301   -- 301 Moved Permanently
  | .found302 => 302   -- 302 Found
  | .temp307 => 307    -- 307 Temporary Redirect
  | .perm308 => 308    -- 308 Permanent Redirect
```

- **REAL / deployed, not a probe.** `Code.status` is called by
  `Redirect.redirect` → `Reactor.Stage.Redirect.redirectFor` / `redirectStage`,
  and `redirectStage` sits at **position 6 of
  `Reactor.Deploy.deployStagesFull2`** — the real ten-stage orb serve
  (`Reactor/Deploy.lean:1496`, "used verbatim"). It is the redirect-status pick
  of RFC 9110 §15.4, one of the candidate fragments the task named.
- **Genuinely loop-free.** A total `match` on the 4-constructor `Code` enum — no
  recursion, no `While`, straight-line branch. (Contrast the same file's
  `render`, which folds over a token *list* — that one has a loop and is
  deliberately NOT what we picked.)

**Faithful lowering.** The `Code` enum is encoded as a tag word `code`:
`moved301=0, found302=1, temp307=2, perm308=3`. Then `Code.status` is
byte-identical to the HOL spec `redirectStatus` (`redirectCoreScript.sml`):

```
⊢ ∀code. redirectStatus code =
    if code = 0 then 301 else if code = 1 then 302
    else if code = 2 then 307 else 308
```

The `.pnk` implementation (`redirectstatus.pnk`, leanc's artifact) is the
matching **equality dispatch** — `if code == 0 { result = 301 } else { … }`.

## 2. THE closed theorem (verbatim, `redirectEndToEndTheory`)

```
[oracles: DISK_THM] [axioms: ]
⊢ (compile_prog_max c mc redirectStatusProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
   FDOM s.eshapes = FDOM (get_eids (functions redirectStatusProg)) ∧
   backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
   mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
   … the standard CakeML heap/bitmap/register-layout + alignment package … ∧
   s.ffi = ffi ∧ (mc.target.config.big_endian ⇔ s.be) ∧
   OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names ∧
   pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
     (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
  redirectFFI code s ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (redirectStatus code)) F) rb])}
```

**Verified** (`verifyRedirectScript.sml`, machine-checked):
`oracles = [DISK_THM]`, `axioms = []`, `hyps = 0`. `DISK_THM` is the benign
disk-export tag on every CakeML theory — no `cheat`, no `mk_thm`, no axiom,
identical trust footing to C11–C15.

**Reading it.** Under the standard CakeML machine-state install package (taken
**verbatim** from `redirectStatusProg_linkB`'s antecedent) and the single
FFI-oracle contract `redirectFFI code s`, **every** observable behaviour of the
installed x64 machine code is the **single** terminating trace whose reported
word is **exactly** `n2w (redirectStatus code)` — the drorb Lean spec
`Redirect.Code.status` applied to the redirect `Code` (encoded tag).

**leanc is OUT of the TCB.** `redirectStatusProg` is the **verified** parser's
output on the emitted bytes: `redirectStatusProg_is_parser_output`,
`oracles=[DISK_THM] axioms=[]`.

## 3. THE bespoke core proof — 2 lines (transferred from C15 unchanged)

The Link-A core `evaluate_redirectCore` — the refinement that cost `boundScan`
**629** lines and `step` **55** — is discharged by **one** call of the reusable
tactic, its only per-primitive inputs the three definitional theorems and the
finite equality-guard list:

```
Theorem evaluate_redirectCore:
  redirectRel code r0 s ⇒
  evaluate (redirectCore, s) =
    (NONE, set_var «result» (ValWord (n2w (redirectStatus code))) s)
Proof
  panLinkA_branch_eq (redirectRel_def, redirectStatus_def, redirectCore_def)
    [“code = 0n”, “code = 1n”, “code = 2n”]
QED
```

`[oracles: DISK_THM] [axioms: ]`. **Zero bespoke tactic steps** — a library-tactic
call, exactly the C15 cost.

| primitive | shape | bespoke Link-A core proof |
|---|---|---:|
| C13 `boundScan` | bounds + scan-`While` | **~629 lines** |
| C14 `step` | 2-guard/3-leaf nested `If` | **~55 lines** |
| C15 `statusClass` (toy) | 4-guard/5-leaf **`<`** cascade | **~2 lines** (`panLinkA_branch`) |
| **C17 `Redirect.Code.status` (REAL, deployed)** | 3-guard/4-leaf **`==`** dispatch | **~2 lines** (`panLinkA_branch_eq`) |

## 4. Did the automation transfer? — YES, with ONE named real-serve friction

**The friction (the real finding).** Real deployed serve code branches on
**algebraic types** (`Code`, `Method`, `ErrClass`), and a `match` on an enum
lowers to an **equality dispatch on the constructor tag** — the Pancake parser
emits `Cmp Equal (Var Local «code») (Const 0w)`, not the `Cmp Less` of C15's
ordered classifier. C15's tactic (`panLinkA_branch`) and its `eval_lt_pinned`
lemma are built for `<` guards only. **This is the genuine gap between a toy
ordered cascade and real serve code.**

**The fix — one program-agnostic extension, added once, reusable forever.** The
equality companion to C15's `<`-machinery:

- `panAutoScript.sml` (+3 theorems, program-agnostic): `eq_n2w64` (word `=` ↔ nat
  `=` in range), `eval_eq_pinned` (the generic `Cmp Equal` guard-evaluator —
  mirror of `eval_lt_pinned`), `evaluate_If_eq`.
- `panAutoLib.sml` (+1 ML tactic): `panLinkA_branch_eq` — byte-for-byte
  `panLinkA_branch` with the guard kind swapped (`dest_eq`/`Cmp Equal`/
  `eval_eq_pinned`). Everything else — `evaluate_If_reduce`, `cond1w_ne0`,
  `Annot_Seq_eval`, `evaluate_Assign_const`, the finite leaf case-split — is
  guard-agnostic and reused unchanged. Built first try; the core closed the
  first time it ran.

This is **~80 lines of reusable metatheory added once**, closing for **any**
future algebraic-type-dispatch (`match`) fragment. The **per-primitive** bespoke
proof stayed **0** (a 2-line tactic call).

**What transferred VERBATIM (the strong result).** Because the decision core is
consumed as a **black box** (`evaluate_redirectCore_framed`), the ENTIRE rest of
the descent is **guard-agnostic** and moved to the real fragment with **zero
proof changes** — only mechanical `status→redirect` renames:

- **The whole-program wrapper** (`redirectMainRefineScript.sml`, 208 lines): the
  control-block layout is **identical** to C15's `statusClass` — N=1 read (one
  input word, the tag), store/report at **+8w**. Not one tactic line changed.
- **`redirectWrapperScript.sml`** (FFI-oracle contract + ML-surgery mainBody),
  **`redirectSemScript.sml`** (clock-lift), **`redirectInstallScript.sml`**
  (single-Function install), **`redirectEndToEndScript.sml`** (final
  composition): all guard-agnostic templates, transferred verbatim.
- **Link B** by the SAME `mk_linkB` generator — one call, `.pnk` filename +
  program name (`redirectLinkBInstScript.sml`, `redirectstatus.pnk`,
  `redirectStatusProg`).
- The emitted core AST (Annot location strings and all) was **dumped from the
  verified parser and transcribed exactly** — no hand-invention; the wrapper's
  ML `Term.subst` fires against it, confirming `redirectCore_def` IS a subterm of
  the parser's `functions redirectStatusProg` body.

**Verdict:** the loop-free descent machinery is **program-agnostic across a
guard-kind change and a jump from toy to deployed code**. The only real-serve
cost was recognising that enum-dispatch = equality guards and adding the
equality companion **once**; after that the real fragment cranked through with
the C15 line budget.

## 5. Line ledger (per-span, spec→machine-code)

| component | lines | kind |
|---|---:|---|
| bespoke core `Proof` (`evaluate_redirectCore`) | **2** | per-primitive (library-tactic call) |
| `redirectCoreScript.sml` total (spec + verbatim core `Def` + relation + framing) | 106 | declarations (irreducible inputs) |
| equality-guard extension (`eval_eq_pinned` &c. + `panLinkA_branch_eq`) | ~80 | **reusable, added ONCE** (new guard kind) |
| `panAuto` + `panAutoLib` + `c14Generic` (the C15 reusable machinery) | ~570 | **reusable, carried with ZERO new proof** |
| wrapper / Sem / Install / EndToEnd / LinkB templates | ~478 | template, `status→redirect` rename only |

Genuinely **bespoke per-primitive proof residual: 0** (the core `Proof` is a
library call). The residual per-primitive **work** is declarations + a
two-parameter wrapper template edit (read-count N, result offset) — here
**identical to C15's** (N=1, +8w), so even that was free.

## 6. Trust ledger (unchanged footing from C13–C15; none of it is leanc)

1. **HOL4 + CakeML kernels.** Every C17 theory is `[oracles: DISK_THM]
   [axioms: ]`, 0 cheats. `redirectStatus` is byte-identical to drorb
   `Redirect.Code.status` under the constructor-tag encoding.
2. **The standard CakeML machine-state install package** — taken **verbatim**
   from `redirectStatusProg_linkB`'s antecedent; the backend correctness
   consuming it is C11's fully-built `pan_to_target_compile_semantics`.
3. **The single FFI-oracle contract `redirectFFI`** — `@load_vec` stages the one
   control word `code` (the encoded `Code` tag); `@report_vec` emits the result
   word onto the trace. The one irreducible honest assumption, structurally
   identical to C15's `statusFFI`.

## 7. Files (`docs/engine/probes/compiler/hol-c17/`)

- `redirectstatus.pnk` — the emitted redirect-status pick (leanc's artifact;
  verified parser's input). Equality dispatch on the `Code` tag.
- `panAutoScript.sml` — REUSABLE program-agnostic theory; **C17 adds `eq_n2w64`,
  `eval_eq_pinned`, `evaluate_If_eq`** (the equality-guard companion).
- `panAutoLib.sml` — REUSABLE automation; **C17 adds `panLinkA_branch_eq`** (the
  equality-dispatch Link-A tactic). `mk_linkB` unchanged.
- `c14GenericScript.sml` — program-agnostic descent machinery, byte-identical to
  C15.
- `redirectCoreScript.sml` — spec `redirectStatus_def` (= `Redirect.Code.status`),
  verbatim core `redirectCore_def` (dumped from the parser), relation, and
  `evaluate_redirectCore` **derived by the library tactic** (2-line proof).
- `redirectLinkBInstScript.sml` — Link B via **one `mk_linkB` call**.
- `redirectWrapperScript.sml` / `redirectMainRefineScript.sml` /
  `redirectSemScript.sml` / `redirectInstallScript.sml` /
  `redirectEndToEndScript.sml` — the guard-agnostic templates (N=1, +8w),
  transferred verbatim from C15.
- `verifyRedirectScript.sml` — the machine-checked oracle/axiom audit.
- `Holmakefile` — INCLUDES the CakeML pancake/backend/proofs dirs; build with
  `CAKEMLDIR=~/src/cakeml`.

## 8. Verdict

- **Does the loop-free descent automation reach the DEPLOYED serve?** **Yes.**
  `redirectEndToEnd$redirect_machine_code`, `[oracles: DISK_THM] [axioms: ]`, 0
  axioms, 0 cheats, green on hbox: the installed x64 machine code emitted for the
  real, deployed redirect-status pick can only ever report the exact drorb Lean
  spec word `n2w (Redirect.Code.status code)`.
- **Bespoke hand-proof for the branch core:** **2 lines** — one
  `panLinkA_branch_eq` call (C15 line budget), on REAL serve code.
- **Did the automation transfer cleanly?** **Yes, with one named friction:** real
  serve code dispatches on algebraic-type tags → **equality** guards, needing a
  ~80-line program-agnostic equality companion, **added once**. After that the
  core, the whole wrapper/Sem/Install/EndToEnd chain, and Link B all transferred
  — the wrapper **verbatim** (same N=1/+8w control block), the core as a 2-line
  library call. The front-end reaches the serve.
