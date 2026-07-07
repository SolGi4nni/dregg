# C3 REPORT — the fold/scan `While` is now preservation-proven: Link A for a LOOP by full loop-invariant induction over panSem's clocked `While`

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**Status: DONE — the loop, in full. A general loop-invariant induction over
`panSem`'s clocked `While` proves that the emitted stream loop refines the Lean
fold `FOLDL mstep` over an input byte stream of ANY length, threading the
byte-memory `LoadByte` relation per iteration and composing the C2 single-step
theorem verbatim as the loop body. Nine kernel-checked HOL4 theorems, every one
`[oracles: DISK_THM] [axioms: ]`, `axioms "machineLoopLinkA" = 0` — no cheats, no
oracles, no extra axioms, against the REAL `panSemTheory`.**

## Verdict in one paragraph

C1 and C2 each closed Link A (Lean model ⇔ `panSem$evaluate`) for a SINGLE
transition and each named the SAME residual UNCLOSED: the fold/scan `While` loop
plus its per-iteration byte-memory `LoadByte` relation — "a loop-invariant
induction over `panSem`'s clocked `While` clause," the multi-day long pole. C3
discharges it. The deliverable is `hol-c3/machineLoopLinkAScript.sml`, a HOL4
theory that builds the machine's stream loop as a real `panLang$prog` `While`
(guard `i < len`; body = `LoadByte (base+i)` → the C2 step body `stepBody`
imported verbatim → `i := i+1`) and proves, against the actual
`panSem$evaluate`, that running the emitted `While` from an invariant state
computes EXACTLY the Lean fold:

> **`machineLoop_fold_bounded`** — `∀k input bs c i s. loopInv input bs c i s ∧
> LENGTH input − i ≤ k ∧ LENGTH input − i ≤ s.clock ⇒ ∃s'. evaluate
> (machineLoop,s) = (NONE,s') ∧ FLOOKUP s'.locals «c» = SOME (ValWord (n2w
> (FOLDL mstep c (DROP i input))))`
>
> **`machineLoop_refines_run`** — from index 0, accumulator 0, with clock ≥
> `LENGTH input`: `evaluate (machineLoop,s) = (NONE,s') ∧ FLOOKUP s'.locals «c»
> = SOME (ValWord (n2w (FOLDL mstep 0 input)))`.

`FOLDL mstep 0 input` is the HOL twin of the Lean model's `C2.run`. This is the
**general-clock induction** — quantified over all input lengths and all
sufficient clocks — not a fixed unrolled iteration count. It is the composition
mechanism the single-step theorems structurally could not exhibit: the C2 step
lemma `evaluate_stepBody` is used **verbatim** as the loop body, and the
`loopInv` state relation (the C2 `mRel` lifted, plus the byte-memory relation) is
carried across every iteration as the induction invariant.

---

## 1. What was proven (against the real `panSem`)

Theory `machineLoopLinkA`, `Holmake` green as `machineLoopLinkATheory [1/1] OK`
against the just-built `panSemTheory` (the real Pancake operational semantics),
CakeML `ed31510b3` (2026-06-29), HOL4 `a9846ebe2` (Trindemossen 2, 2026-07-02),
Poly/ML 5.9.2. It **composes the C2 theory**: `machineStepLinkATheory` is a build
dependency, and `stepBody`, `evaluate_stepBody`, `mstep`, `mstep_le`, `mRel`,
`signed_lt_n2w64` are all opened and reused unchanged. Every theorem carries
`[oracles: DISK_THM] [axioms: ]`; `axioms "machineLoopLinkA" = 0`. Full
statements in `hol-c3/verify_out.txt`.

**The emitted loop** (`machineLoop`, a real `panLang$prog`):
```
While (Cmp Less (Var Local «i») (Var Local «len»))
  (Seq (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»])))
   (Seq stepBody                                    (* the C2 step body, verbatim *)
        (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))))
```

**The byte-memory `LoadByte` relation** (`memRel`) — the item C1 §4-A-3 / C2 §6
named unbuilt: the REAL `panSem` word-addressed byte memory, read at the i-th
buffer address, yields the i-th model byte:
```
memRel input bs s ⇔
  ∀j. j < LENGTH input ⇒
      mem_load_byte s.memory s.memaddrs s.be (bs + n2w j) = SOME (n2w input❲j❳)
```

**The loop invariant** (`loopInv`) — the C2 state relation lifted to the loop:
`«c»` holds the running accumulator `n2w c`, `«i»` the index, `«len»`/`«base»`
the length/buffer address, `«b»` a declared word slot, `memRel input bs s`
holds, and the side conditions `c ≤ 255`, `i ≤ LENGTH input`,
`LENGTH input < 2^63` (the signed-guard range), `EVERY (λx. x<256) input`.

| theorem | what it says (all `[oracles: DISK_THM] [axioms: ]`) |
|---|---|
| **`w2w_byte`** | `x < 256 ⇒ (w2w ((n2w x):word8):word64 = n2w x)` — the width side of the byte read: a memory byte widened to the machine word is the same nat. |
| **`Seq_NONE`** | `evaluate (p1,s)=(NONE,sa) ∧ sa.clock=s.clock ∧ evaluate (p2,sa)=(NONE,sb) ⇒ evaluate (Seq p1 p2,s)=(NONE,sb)` — the `Seq` `fix_clock` collapses to identity for clock-preserving NONE statements. |
| **`eval_loadbyte`** | `loopInv … ∧ i<LENGTH input ⇒ eval s (LoadByte (base+i)) = SOME (ValWord (n2w input❲i❳))` — real `panSem$eval` of the per-iteration byte read = the i-th model byte, via `memRel` + `w2w_byte`. |
| **`evaluate_loopBody`** | `loopInv … ∧ i<LENGTH input ⇒ ∃s2. evaluate (loopBody,s)=(NONE,s2) ∧ s2.clock=s.clock ∧ loopInv input bs (mstep c input❲i❳) (i+1) s2` — ONE iteration: reads the byte into `«b»`, runs the C2 step (writing `n2w (mstep c byte)` via `evaluate_stepBody`), advances `«i»`, and RE-ESTABLISHES the invariant at the next `(accumulator, index)`. **This is where the C2 single-step theorem is composed.** |
| **`machineLoop_unfold`** | `loopInv … ∧ i<LENGTH input ∧ s.clock≠0 ⇒ ∃s2. evaluate (machineLoop,s)=evaluate (machineLoop,s2) ∧ loopInv input bs (mstep c input❲i❳) (i+1) s2 ∧ s2.clock=s.clock−1` — one step of the clocked `While`: the guard fires, one clock tick is spent, the body runs, and the loop reduces to itself at the next state. |
| **`machineLoop_fold_bounded`** | **THE LOOP** — the general loop-invariant induction (∀k): with clock ≥ the remaining iteration count, running the emitted `While` from `(c,i)` terminates and leaves `«c» = n2w (FOLDL mstep c (DROP i input))`. |
| **`machineLoop_refines_run`** | **the headline** — from `(0,0)` with clock ≥ `LENGTH input`, the emitted `While` computes `n2w (FOLDL mstep 0 input)` = the Lean `C2.run` over the whole stream. |

## 2. Why this is the item C1/C2 deferred, and how it is genuinely a LOOP

C1's `evaluate_boundsChk` and C2's `stepBody_refines_step` are **single** moves:
one decision / one transition, universally quantified over the input but with
**no iteration**. C3's `machineLoop_fold_bounded` is a **fixpoint over a clocked
`While`**. Three things make it the real loop proof, not a dressed-up single
step:

1. **General-clock induction over the clocked `While`.** The proof inducts on a
   bound `k` for the remaining iteration count (`Induct_on k`). Each inductive
   step unfolds one `While` iteration (`machineLoop_unfold`) — which threads
   `panSem`'s `dec_clock`/guard bookkeeping (the clocked-semantics substance the
   single-step theorems never touched) — and then applies the induction
   hypothesis at the NEXT accumulator/index. The clock decreases by exactly one
   per iteration because the body has no `Tick`/`While`/`Call`; the hypothesis
   `LENGTH input − i ≤ s.clock` (enough fuel) is what rules out `TimeOut`, and it
   is threaded down the recursion. This holds for arbitrary input length and
   arbitrary sufficient clock — it is NOT a fixed unrolled count.

2. **The byte-memory `LoadByte` relation, threaded.** `memRel` is stated against
   the real `mem_load_byte s.memory s.memaddrs s.be` and is an INVARIANT of the
   loop: the body writes only locals (`«b»`, `«c»`, `«i»`), so
   `s.memory`/`memaddrs`/`be` are untouched and `memRel` survives each iteration
   — proven, not assumed. The per-iteration read `eval_loadbyte` turns the
   relation into the concrete byte `n2w input❲i❳` that the step body consumes.

3. **Composition of the single step.** The loop body theorem `evaluate_loopBody`
   invokes the C2 `evaluate_stepBody` on the mid-iteration state to write the
   data-dependent next accumulator `n2w (mstep c input❲i❳)`, and the fold algebra
   `FOLDL mstep c (input❲i❳::rest) = FOLDL mstep (mstep c input❲i❳) rest` is what
   glues the per-iteration `mstep` into the whole-stream `FOLDL`. The single-step
   theorem is the loop body; this induction is the wrapper — exactly the
   mechanism C1/C2 said the single-step theorems "could not demonstrate."

## 3. The clocked-`While` obstacles that had to be paid (proof notes)

These are the concrete costs the loop carried that the single steps did not, each
now discharged and reusable:

- **`fix_clock` / `dec_clock` accounting.** `panSem`'s `Seq` and `While` wrap the
  recursive call in `fix_clock`. `Seq_NONE` and `fix_clock_id` isolate the fact
  that `fix_clock` is the identity when the body never raises the clock, so the
  big reductions stay clean. (The clean `evaluate_def` `While` clause turned out
  to carry no residual `fix_clock`, so the loop-step reduction threads the body
  result directly.)
- **Unfolding the LEFT `While` only.** `machineLoop_unfold` proves
  `evaluate (machineLoop,s) = evaluate (machineLoop,s2)`; both sides mention
  `machineLoop`, so a naive `once_rewrite` unfolds BOTH and strands the goal. The
  proof uses `CONV_TAC (LAND_CONV (…))` to unfold only the left occurrence one
  step and folds it back with `GSYM machineLoop_def`.
- **`SUC i` vs `i+1` in the fold index.** The list decomposition `DROP i input =
  EL i input :: DROP (SUC i) input` produces `SUC i` where the induction
  hypothesis carries `i+1`; the fold step normalises with `ADD1` so the two
  indices meet. Without this the residual `FOLDL … (DROP (i+1)) = FOLDL … (DROP
  (SUC i))` does not close.

None of these use `cheat`, `new_axiom`, or any oracle; the footprint audit
(`verify_out.txt`) is clean.

## 4. Is a loop now preservation-proven? (the honest verdict)

**Yes — FULLY, for this machine primitive, by general-clock induction.** Not a
bounded/unrolled fallback: `machineLoop_fold_bounded` is quantified over all
input lengths and all sufficient clocks. The `LENGTH input ≤ s.clock` hypothesis
is not a limitation of the proof — it is the standard "give the machine enough
fuel" precondition of CakeML's clocked semantics (the top-level `semantics`
wrapper existentially quantifies the clock; with too little clock the `While`
legitimately `TimeOut`s). Within that standard shape, the loop's Link A is
discharged end-to-end against real `panSem`, with the byte-memory relation
threaded and the C2 step composed.

## 5. What full-engine emission still needs AFTER this

The recurring per-primitive long pole (the loop) is now paid once and the
machinery is reusable, but a whole-engine claim still owes:

1. **Whole-program frame: `Dec` / `Store` / FFI.** `machineLoop` is the `While`
   in isolation. The full `main` (`pnk/machinestep.pnk`) wraps it in `Dec`s that
   initialise `«i»=0`, `«c»=0`, `«base»`, `«len»`, a `Store`, and two FFI calls
   (`@load_vec` fills the byte buffer, `@report_vec` prints the counter) that sit
   OUTSIDE any theorem. A whole-system statement owes the FFI a spec and the
   `Dec`/`Store` frame their evaluate lemmas, and must ESTABLISH `loopInv … 0 0`
   from the `Dec` initialisation and the `@load_vec` postcondition (which is where
   `memRel` would be discharged from the buffer the FFI wrote). C3 assumes
   `loopInv … 0 0` as the loop's precondition; connecting it to `main` is the
   named next step.

2. **The `memRel` altitude.** `memRel` is stated at `mem_load_byte` (the byte
   read result), not unfolded to `get_byte`/`byte_align`/endianness. That is the
   honest interface — the packing that POPULATES the memory is the FFI's job — but
   a full story links `memRel` to whatever `@load_vec`'s C actually writes.

3. **Parser faithfulness.** `machineLoop`/`loopBody`/`stepBody` are the `.pnk`
   transcribed into the `panLang` AST by hand, not derived by running the Pancake
   parser theory (`panPtreeConversion`) on `machinestep.pnk`. Same small, named
   residual as C1/C2.

4. **Link B instantiation.** Discharging the `pancake_good_code`/heap side
   conditions of `pan_to_target_compile_semantics` at `machineLoop` — a checking
   obligation, not new proof — and lifting the clocked theorem to the
   clock-quantified `semantics` statement (mechanical given `machineLoop_fold_bounded`).

5. **Other primitives' bodies.** The loop skeleton (`loopInv`, `Seq_NONE`,
   `machineLoop_unfold`, the `fold_bounded` induction) is primitive-agnostic and
   reusable, but each looping primitive supplies its own single-step body lemma.
   C1's region digest scan `While` is the same loop shape and now inherits this
   mechanism; it still needs its digest step (`*31 + b`) proved as a body lemma
   analogous to `evaluate_stepBody`.

## 6. Files (under `docs/engine/probes/compiler/`)

- `hol-c3/machineLoopLinkAScript.sml` — the theory: `loopBody`/`machineLoop` AST,
  `memRel`, `loopInv`, the helper lemmas, and the loop induction. Opens and
  composes `machineStepLinkATheory` (C2).
- `hol-c3/Holmakefile` — `INCLUDES` for the CakeML `pancake`,
  `pancake/semantics`, `compiler/backend`, `compiler/encoders/asm`, `misc`,
  `semantics/ffi` dirs.
- `hol-c3/verify_out.txt` — the printed theorem statements + `[oracles]`/
  `[axioms]` tags and the `axioms = 0` footprint audit.

## 7. Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`:
```
export CAKEMLDIR=$HOME/src/cakeml
export PATH=$HOME/src/HOL/bin:$PATH
# work dir must contain: Holmakefile, machineStepLinkAScript.sml (C2, copied),
#                        machineLoopLinkAScript.sml (C3)
cd <workdir> && Holmake machineLoopLinkATheory.uo   # builds C2 then C3, green
```
`panSemTheory` and its dependency chain build from the CakeML tree in well under
a minute on hbox; C2 compiles in ~5 s and C3 in ~5 s. `verify_out.txt` is
regenerated by loading `machineLoopLinkATheory` with `Globals.show_tags := true`.

## 8. Bottom line for Phase C

The compiler lane's dominant remaining lever — "the fold/scan `While` … named
UNCLOSED in both C1 and C2: the loop-invariant induction over `panSem` clocked
`While` + the byte-memory relation" — is now **preservation-proven in full** for
the C2 machine primitive: a general-clock loop-invariant induction over the real
clocked `While`, threading the real byte-memory `LoadByte` relation, composing
the C2 single-step theorem verbatim, kernel-checked with a clean footprint. The
per-primitive multi-day long pole is paid once; what remains for whole-engine
emission is the whole-program `Dec`/`Store`/FFI frame that establishes the loop's
precondition from `main`, plus the standing named residuals (parser
faithfulness, Link B instantiation) — engineering and checking, no longer an open
loop-induction research item.
