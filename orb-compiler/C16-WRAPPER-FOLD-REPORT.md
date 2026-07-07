# C16 REPORT — the loop-free wrapper is now a mechanical GENERATOR (reproduces C14 **and** C15 whole-program wrappers automatically), and the LOOP class opens: a reusable **fold-loop schema** closes a NEW fold primitive's whole Link-A loop core from a **~8-line per-step fill-in**, not boundScan's 629-line invariant — every theorem `[oracles: DISK_THM] [axioms: ]`, 0 axioms, 0 cheats, kernel-checked, `~/hol-c16` green on hbox

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C15 used.

**Two deliverables, both closed.** C15 automated the *loop-free core* (a reusable
decision tactic `panLinkA_branch`) and Link B (the `mk_linkB` generator), leaving
the *whole-program wrapper* as a hand-edited template and *loops* entirely hand-
proved. C16 (1) turns that wrapper template into a mechanical **`mk_wrapper`
generator** — demonstrated by reproducing BOTH C15's status wrapper (N=1 read,
+8w result) AND C14's step wrapper (N=2, +24w) with the read-count and offset as
the only parameters — and (2) opens the **loop class** with a reusable
**fold-loop schema** (`foldLoop_bounded`/`foldLoop_refines`) whose single obligation
a NEW fold primitive discharges with a per-step fill-in, demonstrated end-to-end
on a running **byte-sum** scan.

Everything rebuilt on hbox `~/hol-c16` (`Holmake` exit 0, 12 theories); `axioms`
= 0 for all of `foldLoopSchema, statusGen, stepGen, verifyC16, c14Generic, panAuto`.

---

## 1. DELIVERABLE 1 — the whole-program wrapper GENERATOR (`mk_wrapper`)

`panWrapperLib.mk_wrapper` (ML, 482 lines, program-agnostic; no metatheory) closes
the last automation gap named in C14 §4.2 / C15 §6: it produces the **entire**
wrapper stack — `MainRefine` + `Sem` (`call_main_run`/`main_semantics`) +
`Install` (`semantics_decls`) + `EndToEnd` (`machine_code`) — from parameters, by
**folding over the emitted N-read `Dec` spine** (`mk_mainRefine`) and running the
uniform Sem/Install/EndToEnd stages by `prove` from parameterized goals. The
per-primitive inputs are exactly: the parsed program + its Link B, the core Link-A
theorem (framed + noFFI), the relation/ctrl-block/FFI decls, the **read list**
(local names + pinned num-vars), the **buf offset**, and the **result-store offset**.
No proof is written by hand per primitive.

**It reproduces BOTH prior whole-program wrappers, from the SAME generator:**

| demo (script) | primitive | reads N | result offset | generated theorem | tag |
|---|---|---:|---:|---|---|
| `statusGen` | HTTP status classifier | 1 (`code`) | +8w | `status_machine_code` | `[oracles: DISK_THM] [axioms: ]` |
| `stepGen` | branch-only machine step | 2 (`c`,`b`) | +24w | `step_machine_code` | `[oracles: DISK_THM] [axioms: ]` |

`verifyC16` prints both and confirms `axioms statusGen = 0`, `axioms stepGen = 0`,
`axioms verifyC16 = 0`. The generated `status_machine_code` is byte-identical to
C15's hand `statusEndToEnd$status_machine_code` (installed x64 can only report
`n2w (statusClass code)`); `step_machine_code` byte-identical to C14's
(`n2w (mstep c b)`). Both also emit `statusMainBody_refines` / `stepMainBody_refines`
(the whole-`main` FFI-trace refinement) — the previously hand-written 100+-line
`MainRefine` proofs, now generated.

The two demos differ **only** in the parameter record (`reads`, `bufOff`, `koff`,
`specWord`, the core/relation/prog names). The read-count N (1 vs 2) and result
offset (+8w vs +24w) — the exact two knobs C15 §6 named as the residual — are now
the generator's arguments. **The loop-free class is fully mechanical, core to
machine code.**

## 2. DELIVERABLE 2 — the FOLD-LOOP SCHEMA (the loop class opens)

`foldLoopSchemaScript.sml` is a **program-agnostic** theory capturing the bounded-
fold-over-array loop invariant that cost boundScan (C13) a 629-line hand-derivation.

**The schema (reusable, proved once).** For a byte array `input` at base `bs`, with
the loop invariant `foldInv` (locals `«i»/«acc»/«len»/«base»` pinned, byte memory
related by `memRel`, `i ≤ |input|`, `|input| < 2^63`), and a machine-word
accumulator (exact — no `n2w`-faithfulness side condition):

```
[oracles: DISK_THM] [axioms: ]
⊢ foldLoop_refines
  !accf body input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (body,s) = (NONE,s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !init s. foldInv input bs 0 init s /\ LENGTH input <= s.clock ==>
      ?s'. evaluate (While foldGuard body, s) = (NONE, s') /\
           FLOOKUP s'.locals «acc» =
             SOME (ValWord (FOLDL accf init (MAP (\c. n2w c) input)))
```

From **one** per-step obligation (`body_step`: an iteration advances the
accumulator by `accf acc (n2w byte)` and preserves the invariant + clock), the
whole clocked-`While` computes **exactly** the Lean fold `FOLDL accf init` over the
byte array — the spec of ANY running-accumulator scan. Proved by clocked induction
on the fuel bound `|input| - i ≤ k`, one `While`-unfold per iteration
(`foldLoop_iter`), reusing the C5/C6 clocked-loop machinery (`memRel`, `w2w_byte`,
`fix_clock_id`, `DROP_EL_CONS_local`) re-declared self-contained + `signed_lt_n2w64`
from the C15 program-agnostic `panAuto`. `[oracles: DISK_THM] [axioms: ]`.

**Demonstration on a NEW fold-loop primitive — running byte-SUM — CLOSED loop core:**

```
[oracles: DISK_THM] [axioms: ]
⊢ sumLoop_refines
  !input bs init (s:(64,'ffi) state).
    foldInv input bs 0 init s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (While foldGuard sumBody, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» =
           SOME (ValWord (FOLDL sumAcc init (MAP (\c. n2w c) input)))
```

where `sumAcc a b = a + b` and `sumBody` is the emitted body
(`Assign «b» (LoadByte (base+i)); Assign «acc» (acc + b); Assign «i» (i+1)`). The
installed byte-sum `While` provably computes exactly `FOLDL (+) init (MAP n2w input)`
= `init` + the byte sum. `[oracles: DISK_THM] [axioms: ]`, 0 cheats.

### The per-step fill-in vs boundScan's 629

| primitive | loop core Link-A proof | kind |
|---|---:|---|
| C13 `boundScan` | **~629 lines** | synthesise + prove a bespoke loop invariant (`digInv`, a `FOLDL`-digest over a `LoadByte` mem-relation) by hand |
| **C16 `sumBody` (byte-sum)** | **~21 lines** (`sumBody_step` statement + proof; ~8 bespoke tactic lines) | one forward evaluation of the emitted body + re-establish `foldInv` at `i+1`; the loop induction is the reusable schema |

`sumBody_step` (the fill-in) is a single `evaluate` of the three `Assign`s using the
generic `eval_foldByte` byte-read lemma, then `foldInv` re-established at `i+1` by
`simp`. **No invariant synthesis, no clocked induction per primitive** — those are
in the schema. That is a ~30× shrink and, more importantly, a **change of kind**:
from "invent and prove a loop invariant" to "evaluate one iteration."

## 3. The continuation-hint break — found and FIXED

The 429-killed run left `foldLoop_bounded` failing with a "re-parse artifact." The
in-Script goalstack diagnosis (per the hint) located **two** real causes, neither a
re-parse:

1. **Assumption selection.** The body_step and the induction hypothesis are BOTH
   `!i acc s. … ==> …`. `first_x_assum`/`last_x_assum` both grabbed the **IH**; the
   discriminating `qpat_x_assum \`!i acc s. … i < LENGTH input ==> _\`` raised a raw
   SML **`Match`** in the faithful type environment (a matcher edge on a quantified
   pattern with a `_` wildcard) — the "artifact." **Fix:** isolate the iteration in a
   separate lemma `foldLoop_iter` (body_step as its own antecedent, so it is the sole
   forall), and drive the main induction with `disch_then`, keeping body_step a NAMED
   hypothesis OUT of the assumption list and applying it via `MATCH_MP foldLoop_iter
   bstep` — so the IH is the unique forall for `last_x_assum`.
2. **Untied state type variable.** body_step's state and the conclusion's state
   generalized to *independent* ffi type variables; an instantiated precondition
   `foldInv … s2` then **printed identically to its own assumption but was not
   α-convertible** (a spurious `(64,'a)` vs `(64,'b)` mismatch), so `fs []` could
   not discharge it. **Fix:** tie every bound state to one shared `(64,'ffi) state`
   annotation across both theorems (and constrain the accumulator byte to `word64`,
   which the loop-free `MAP (λc. n2w c :word64)` had pinned but the isolated lemma
   had not).

With both fixed, `foldLoop_iter`/`foldLoop_bounded`/`foldLoop_refines` and the
byte-sum demonstration all build green, 0 axioms.

## 4. Residual + path to real serve fragments

**What is closed.** Loop-free primitives: whole descent AUTOMATIC (core tactic +
`mk_wrapper` + `mk_linkB`). Loop primitives: the **loop CORE** (the Link-A body —
emitted `While` = `FOLDL` spec) is now a **per-step fill-in** via the schema.

**The named residual — the loop WRAPPER.** `sumLoop_refines` closes the loop core
but not the whole-program spec→machine-code stack for a loop primitive. Two gaps,
both scoped, neither new metatheory:
- **`mk_wrapper` needs a fuel-budget parameter.** The loop-free generator threads a
  fixed nonzero clock; a loop primitive's `MainRefine` must instead thread
  `LENGTH input ≤ s.clock` (the schema's clock precondition) through Sem/Install/
  EndToEnd. This is one extra parameter on `mk_mainRefine` + the C13 boundScan loop
  wrapper as the template — mechanical, no new proof.
- **The array read.** The loop reads a *pointer + length* (not N scalar words); the
  ctrl-block/FFI contract gains an array-staging clause (boundScan already has the
  shape).

**Path to real serve fragments.** The fold-loop class is precisely the datapath-scan
shape: chunk-length scans, transfer-encoding/`Content-Length` digests, header
byte-classification, checksum/CRC-step, running-max. C13 `boundScan` already closed
a bounds+scan; the schema now makes *any* running-accumulator scan over a byte array
(sum/XOR/max/CRC-step) a ~8-line fill-in. The route to a verified serve datapath:
emit each scan primitive from the Pancake datapath, express its body as a `foldInv`
step, discharge via a `sumBody_step`-style fill-in, compose via `foldLoop_refines`,
then wrap with the fuel-budgeted `mk_wrapper` (the residual above). The reusable
surface — `panAuto` + `panAutoLib` (loop-free core + `mk_linkB`) + `panWrapperLib`
(`mk_wrapper`) + `foldLoopSchema` (loop core) — is the front-end a generated engine
would call; the remaining hand-work per primitive is declarations + one per-step
fill-in.

## 5. Trust ledger (unchanged from C13–C15; none of it is leanc)

Every C16 theory is `[oracles: DISK_THM] [axioms: ]`, `axioms = 0`, 0 cheats.
`DISK_THM` is the benign CakeML disk-export tag — no `cheat`, no `mk_thm`, no axiom.
The generated `machine_code` theorems consume the standard CakeML machine-state
install package **verbatim** and C11's fully-built `pan_to_target_compile_semantics`;
leanc stays OUT of the TCB (verified parser output). The fold-loop schema adds no
new trust: its accumulator is an exact machine word, and it rests only on the
re-declared C5/C6 clocked-loop machinery + `panAuto`.

## 6. Files (`docs/engine/probes/compiler/hol-c16/`, built on hbox `~/hol-c16`)

- `panWrapperLib.sml` — **THE `mk_wrapper` GENERATOR (ML, 482 lines)**: whole-program
  wrapper (MainRefine fold over the N-read `Dec` spine + Sem/Install/EndToEnd stages),
  read-count N and result offset as parameters.
- `statusGenScript.sml` / `stepGenScript.sml` — the two demos: `mk_wrapper` reproduces
  C15's status wrapper (N=1/+8w) and C14's step wrapper (N=2/+24w) automatically.
- `verifyC16Script.sml` — prints both generated `machine_code` + `mainBody_refines`
  theorems with tags; asserts `axioms = 0`.
- `foldLoopSchemaScript.sml` — **THE FOLD-LOOP SCHEMA**: `foldInv`, `foldLoop_iter`,
  `foldLoop_bounded`, `foldLoop_refines` (reusable) + `sumAcc`/`sumBody`/`sumBody_step`
  /`sumLoop_refines` (the byte-sum demonstration, closed loop core).
- `panAutoScript.sml` / `panAutoLib.sml` / `c14GenericScript.sml` — the C15 reusable
  program-agnostic theory + tactics + descent machinery the wrappers rest on.
- `statusCore/statusWrapper/statusLinkBInst` + `stepCore/stepWrapper/stepLinkBInst`
  + `statusclass.pnk` / `machinestep_gate.pnk` — the two primitives' cores/decls
  (verified-parser inputs) the generator consumes.
- `Holmakefile` — INCLUDES the CakeML pancake/backend/proofs dirs + `~/c2`; build with
  `CAKEMLDIR=~/src/cakeml`.
