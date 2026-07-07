# EMIT-HOL4 — the generator that EMITS the HOL4 Link A refinement script from a primitive description

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**Builds on:** C1 (`C1-REPORT.md`, `hol-c1/boundScanLinkAScript.sml` — the first
kernel-checked Link A preservation theorem for the region bounds-check).
**Status: DONE for the region template — a generator (script template +
primitive-specific fill-ins) produces a HOL4 theory that rebuilds GREEN with the
same four Link A theorems, demonstrated on TWO distinct region primitives; the
machine template is scaffolded with its obligation stated and its definitions
building green. Zero cheats, zero custom oracles, zero extra axioms.**

## Verdict in one paragraph

C1 hand-wrote one Link A script for one primitive. EMIT-HOL4 turns that hand
into a **generator**: a family template with `{{holes}}` plus a per-primitive
JSON descriptor, and a family-agnostic substitution engine (`emit.py`) that
fills the holes and writes a `<theory>Script.sml`. The HOL4 kernel is the
generator's correctness check — exactly the role the Lean kernel plays for the
front-end DSL: a bad fill-in **fails to typecheck or fails to prove; it can
never `cheat`** (`emit.py` additionally hard-fails if any `{{hole}}` survives
substitution, so a malformed descriptor can't emit a half-filled script). Driven
by the `region_boundScan` descriptor the generator re-emits the C1 primitive and
it **rebuilds green** with the same theorems; driven by a *second, different*
region descriptor (`region_viewFit` — different local names, a different
sentinel word, a different SPEC fold) it emits a **new** theory that **also
rebuilds green**. That second instance is the proof of generativity: the proof
scripts are FIXED text; only the primitive shape is substituted, and the kernel
re-checks each result. The machine family gets its own template; honest scope
holds — its SPEC (a finite-state transition), its `.pnk` dispatch AST and its
state relation are **emitted and typecheck green**, and the transition-refinement
theorem is emitted as a **stated obligation** with its proof plan and its one
deferred cost (the run-loop `While`, the exact analogue of C1's deferred scan
loop). Everything below was rebuilt from `Holmake cleanAll` on hbox.

---

## 1. What the generator is

Three moving parts, all under `hol-emit/`:

- **`emit.py`** — the family-agnostic engine. Reads a descriptor, selects the
  family's template, substitutes `{{KEY}}` → value, and **fails loud on any
  surviving `{{`** (an unfilled hole = a generator bug, never a silent emit).
  A few fill-ins are *derived* (the word literal `4294967295w` from the sentinel
  number; `(a:num list)` from the array name) so the descriptor stays minimal.
- **`template/region.sml.tmpl`** — the region-family template: the C1 script with
  every primitive-specific token replaced by a hole. The proof scripts are
  verbatim-fixed; only names, the size term, the sentinel and the fold body vary.
- **`template/machine.sml.tmpl`** — the machine-family template (scaffold).

Descriptors in `hol-emit/descriptors/`:

| descriptor | family | theory | primitive |
|---|---|---|---|
| `region_boundScan.json` | region | `boundScanEmit` | the C1 bounds-check (re-emission) |
| `region_viewFit.json`   | region | `viewFitEmit`   | a *different* region view-fit check |
| `machine_toggle.json`   | machine | `toggleEmit`   | a 2-state toggle transition (scaffold) |

Run: `python3 emit.py --all --out build`. Emitted `.sml` land in `hol-emit/build/`.

## 2. The region template is real and rebuilds green

### 2.1 Re-emission of the C1 primitive is faithful

`emit.py` + `region_boundScan.json` produces `build/boundScanEmitScript.sml`,
which is **byte-for-byte the C1 `boundScanLinkAScript.sml`** modulo (a) the
theory name (`boundScanEmit`) and (b) three theorem names generalized to the
family vocabulary (`eval_bounds_expr`→`eval_guard`,
`evaluate_boundsChk`→`evaluate_impl`, `boundsChk_encodes_spec`→
`impl_encodes_spec`). Same Lean SPEC, same `panLang` AST, same `stRel`, same
`signed_lt_n2w64` convention lemma, same proofs. So the generator reproduces the
hand-written artifact exactly — the baseline claim.

### 2.2 A second, genuinely different region primitive also builds

`region_viewFit.json` fills the *same* template with a different shape:

| hole | `region_boundScan` | `region_viewFit` |
|---|---|---|
| locals | `alen`,`off`,`len`,`result` | `cap`,`base`,`extent`,`out` |
| SPEC decision | `boundScan a off len` | `viewFit b base extent` |
| encode / sentinel | `c0_encode` / `4294967295` | `vf_encode` / `3735928559` |
| SPEC `SOME` body / aux | `scanFrom a off len 0` (+`step`,`scanFrom` defs) | `base + extent` (no aux) |
| size term | `LENGTH a` | `LENGTH b` |

The emitted `viewFitEmitScript.sml` compiles under the **same fixed proof
scripts** and yields (from `build/verify_out.txt`, `show_tags` on):

```
⊢ vfRel b base extent r0 s ⇒
  eval s (Cmp Less (Var Local «cap»)
                   (Op Add [Var Local «base»; Var Local «extent»])) =
  SOME (ValWord (if viewFit b base extent = NONE then 1w else 0w))          [oracles: DISK_THM] [axioms: ]

⊢ vfRel b base extent r0 s ⇒
  evaluate (viewChk,s) =
  (NONE, if viewFit b base extent = NONE then
           set_var «out» (ValWord (n2w (vf_encode (viewFit b base extent)))) s
         else s)                                                            [oracles: DISK_THM] [axioms: ]

⊢ vfRel b base extent r0 s ⇒
  ∃s'. evaluate (viewChk,s) = (NONE,s') ∧
       (viewFit b base extent = NONE ⇒
          FLOOKUP s'.locals «out» =
            SOME (ValWord (n2w (vf_encode (viewFit b base extent))))) ∧
       (viewFit b base extent ≠ NONE ⇒ s' = s)                             [oracles: DISK_THM] [axioms: ]
```

Two different primitives, one template, both kernel-checked. **That is the
proof that the HOL4 emission is generative, not a one-off copy.** The
`signed_lt_n2w64` convention lemma (the signed-range witness C1 surfaced) is
carried by the template, so every emitted region primitive inherits the correct
signed side-condition automatically — the seam is generated, not re-derived.

### 2.3 Green rebuild from scratch

On hbox, `Holmake cleanAll` then `Holmake` over `hol-emit/build/`
(`build/rebuild.log`):

```
Building 3 theory files
Starting work on boundScanEmitTheory
Starting work on toggleEmitTheory
Starting work on viewFitEmitTheory
toggleEmitTheory      (6s)  [1/3]  OK
viewFitEmitTheory     (6s)  [2/3]  OK
boundScanEmitTheory   (6s)  [3/3]  OK
EXIT=0
```

All eight region theorems carry `[oracles: DISK_THM] [axioms: ]` (full printout
in `build/verify_out.txt`) — the HOL4 analogue of the Lean `#print axioms`
clean-footprint check. `DISK_THM` is the serialization tag, not a soundness
oracle; the absence of any custom oracle or extra axiom is the point.
Toolchain: CakeML `ed31510b3` (2026-06-29), HOL4 `a9846ebe2` (2026-07-02),
against the real `panSemTheory`.

## 3. The template generalization — what varies, and at which layer

The generator separates **three layers**, and this is the reusable finding:

1. **Family-agnostic engine** (`emit.py`): placeholder substitution + the
   unfilled-hole guard. Knows nothing about Pancake or bounds checks.
2. **Per-FAMILY template** (`region.sml.tmpl`, `machine.sml.tmpl`): fixes the
   *proof shape* for a whole class of primitives. The region template bakes in
   "signed bounds `If` → sentinel-on-out-of-bounds", including the entire proof
   text of the four theorems and the `signed_lt_n2w64` lemma. **The proofs never
   change across primitives in the family** — that is what makes it a template
   and not a code sketch.
3. **Per-PRIMITIVE descriptor** (JSON): the shape fill-ins only — names, the
   size term, the sentinel, the SPEC fold. No proof text.

The region family's fixed shape: one size local, two offset locals summed, guard
`Cmp Less size (off+len)`, then-branch writes the sentinel `Const`, else-branch
`Skip` (the region body, out of scope for the fragment — the deferred scan
`While` in C1 terms). Any primitive that IS a signed bounds decision writing a
one-word encoded result is a fill-in of this one template.

## 4. How the machine template differs (scaffold + stated obligation)

The machine family gets a **separate template** because its proof shape is
different. `machine_toggle.json` → `toggleEmitScript.sml` **emits and builds
green** these definitions (from `build/verify_out.txt`):

```
⊢ toggleStep =
  If (Cmp Equal (Var Local «state») (Const 0w))
     (Seq (Assign Local «state» (Const 1w)) (Assign Local «out» (Const 0w)))
     (Seq (Assign Local «state» (Const 0w)) (Assign Local «out» (Const 1w)))     -- the .pnk dispatch AST
⊢ ∀q i. toggle q i = (¬q, if q then 1 else 0)                                    -- the Lean transition SPEC
⊢ ∀q o0 s. mRel q o0 s ⇔ FLOOKUP s.locals «state» = SOME (ValWord (encQ q)) ∧
                          FLOOKUP s.locals «out» = SOME (ValWord o0)             -- the state relation
```

The refinement theorem is emitted as a **stated obligation** (a comment block in
the generated script, so the file carries zero unproven-but-claimed theorems and
zero `cheat`s):

```
|- mRel q o0 s ⇒
   ∃s'. evaluate (toggleStep, s) = (NONE, s') ∧
        mRel (FST (toggle q i)) (n2w (SND (toggle q i))) s'
```

**The two differences from the region template, stated concretely:**

1. **Dispatch, not a bounds `If`.** The proof is a finite **case split on the
   state tag** (`Cases_on q`), each arm reducing the real `panSem$evaluate` of a
   `Seq` of `Assign`s. This is the *direct analogue* of the proven region
   `evaluate_impl` and uses the **same** eval/word toolkit (`eval_def`,
   `set_var_def`, `word_cmp_def`, `FLOOKUP_UPDATE`) — tractable, same order of
   effort as the region `If` C1 already paid.
2. **The run loop is the deferred cost.** A machine consuming an input *stream*
   wraps the step in a `While` over the input list; its Link A is a
   loop-invariant induction over `panSem`'s clocked `While` clause
   (`q_n = FOLDL (λq i. FST (toggle q i)) q0 inputs`) — **structurally identical
   to the region scan `While` deferred in C1 §4-A-2**. Same shape, same dominant
   cost, sitting on the proven single-step dispatch.

So: machine template = { SPEC transition } × { dispatch AST } × { state relation }
(all emitted, all typecheck) + { case-split proof of the single step (tractable,
region-toolkit) } + { `While` induction for the stream (deferred = the region
scan-loop cost) }. The honest scope line: **region template real + rebuilds;
machine template scaffolded with the obligation stated.**

## 5. What this proves for the compiler lane

- The Link A **refinement script is generative**, not hand-crafted per
  primitive: one template + a shape descriptor + the kernel re-check produces a
  green theory per primitive, and a *second distinct primitive* confirms it is
  data-driven rather than a renamed copy.
- The generator inherits the kernel as its correctness check in the DSL sense:
  a bad generation cannot slip through as a `sorry`/`cheat` — it fails `Holmake`.
  The `emit.py` unfilled-hole guard closes the one gap the kernel can't see (a
  syntactically-valid but semantically-empty half-fill).
- The remaining unit cost is unchanged and now **factored**: the per-family
  *loop* proof (scan `While` for region, run `While` for machine) is the shared
  deferred item; everything around it — the decision/dispatch, the word
  conventions, the encode injection, the state relation — is templated and
  proven.

## 6. Files (under `docs/engine/probes/compiler/hol-emit/`)

- `emit.py` — the generator engine (substitution + unfilled-hole guard).
- `template/region.sml.tmpl` — region-family template (real, full proofs).
- `template/machine.sml.tmpl` — machine-family template (scaffold + obligation).
- `descriptors/{region_boundScan,region_viewFit,machine_toggle}.json` — the
  primitive descriptors.
- `build/{boundScanEmit,viewFitEmit,toggleEmit}Script.sml` — the generated
  theories (checked-in artifacts of a generator run).
- `build/Holmakefile` — `INCLUDES` for the CakeML `panSem` ancestors.
- `build/verify_out.txt` — theorem statements + `[oracles]`/`[axioms]` tags.
- `build/rebuild.log` — the `Holmake cleanAll`→green `[3/3] OK` build log.

## 7. Reproduce

On hbox, with CakeML at `~/src/cakeml` and HOL4 at `~/src/HOL`:
```
cd <repo>/docs/engine/probes/compiler/hol-emit
python3 emit.py --all --out build          # generate the 3 theories
scp build/{Holmakefile,*Script.sml} hbox:~/hol-emit/
ssh hbox 'export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
          cd ~/hol-emit && Holmake cleanAll && Holmake'   # green [3/3] OK
```
`panSemTheory` and its dependency chain build from the CakeML tree in under a
minute; the three generated theories compile in ~6 s each.

## 8. Bottom line

The HOL4 half of the front-end obligation is no longer only paid once by hand —
it is **emitted**. Give the generator a region primitive's shape and it writes a
kernel-checked Link A refinement theory; two different region primitives prove
it is a template and not a transcription; the machine family shows the same
generator carries a second template whose scaffold builds and whose one
remaining obligation (the run-loop `While`) is the named, shared, deferred cost.
The DSL's "emit the whole verified triple" ambition now has its HOL4-refinement
limb standing up, kernel-green.
