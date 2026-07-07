# C2 REPORT — the MACHINE primitive, emitted and preservation-proven: Link A generalized from a bounds decision to a stateful transition

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for cake/HOL4; local for
Lean. **Status: DONE for the single transition — the emitted saturating-counter
FSM step agrees with the Lean model on every vector (two kernels), and its Link A
(Lean transition ⇔ `panSem$evaluate` of the emitted step) is a kernel-checked
HOL4 theorem, `[oracles: DISK_THM] [axioms: ]`, no cheats/oracles/extra axioms.
The stream `While` fold is named UNCLOSED, exactly as C1's scan loop.**

## Verdict in one paragraph

C0/C1 emitted and preservation-proved a **region** primitive (a bounds decision
over a byte view): C1's `boundScanLinkAScript.sml` is the first kernel-checked
Lean-model ⇔ `panSem` theorem, but it proves a one-shot decision that writes a
**constant** sentinel. C2 takes the **machine** primitive the goal calls for — a
total transition `State → Input → State` — as a **saturating event-counter FSM
step**, and closes the same two deliverables for it. (1) The step is EMITTED as
Pancake (`pnk/machinestep.pnk`), compiled by the verified CakeML/Pancake backend
(`cake --pancake`) to x64, linked, and run: on nine adversarial input streams the
compiled machine's final counter equals the Lean model's `run` **byte for byte**,
including the saturation vectors (300 events → **255, no wrap**). (2) Link A is
**proven in HOL4 against the real `panSem$evaluate`**: `evaluate (stepBody, s)`
updates the state local `c` to **exactly** `n2w (mstep c b)` — the Lean
transition's next state — **and re-establishes the state relation `mRel` at the
new counter**, so the relation is an INVARIANT the emitted step preserves and the
transition composes. That invariance clause is the real generalization over C1:
where C1 wrote a fixed sentinel, C2 proves the emitted step computes a
**data-dependent next state that is a function of the old state**, and that the
step is a well-behaved transition-system move (which carries the saturation
MEANING: the counter never exceeds `CAP = 255`). This also converts the machine
template's **stated obligation** from EMIT-HOL4-REPORT (the toggle
transition-refinement theorem, left as an unproven comment block) into a
**discharged** theorem for a richer machine primitive. What it is **not**: the
stream fold. The whole machine folds the step over an input stream with a
`While`; that loop's Link A — a loop-invariant induction over `panSem`'s clocked
`While` — is **not** proven here and is named UNCLOSED, the exact analogue of
C1's deferred scan loop.

---

## 1. The primitive and why this one

The goal asks to extend the compiler probe from the REGION primitive to the
**MACHINE** primitive: a step function `Input → State → State`, total. C2's is a
**saturating event counter** (`model/MachineStep.lean`, `C2.step`):

> **`step c b`** = `c` if `b < 128` (a "low" byte — HOLD); else, if `c < 255`,
> `c + 1` (a "high" byte is an EVENT — advance); else `255` (SATURATE at
> `CAP = 255`, never overflow).

`run` folds `step` over an input stream from `c = 0`. This is the smallest honest
core of a streaming FSM: a **data-dependent classify** (`If` on the input byte), a
**data-dependent saturating update** (a second `If` on the state), and a **state
carried across the fold**. It is not a toy: the saturation arm is a real safety
property — a counter that wrapped would undercount (300 events would read `44` or
`0`, not `255`).

Why a counter and not the region again: the region Link A (C1) proves a decision
that writes a **constant**. A machine step must prove the emitted code writes the
**next state**, a function of the old state, and that the **state relation is
preserved** so the step can iterate. That is a structurally different, and
stronger, obligation — the transition-system shape the full engine's step
functions actually have.

## 2. Files (all under `docs/engine/probes/compiler/`)

- `model/MachineStep.lean` — the SPEC. Self-contained, Lean core only, no
  Mathlib. Typechecks; `#print axioms C2.step` = *(none)*, `C2.run` = *(none)*,
  `C2.step_le_cap` = `{propext, Quot.sound}` (a strict subset of the allowed
  `{propext, Quot.sound, Classical.choice}`). Total by construction. Includes the
  saturation MEANING theorem `step_le_cap : c ≤ CAP → step c b ≤ CAP`, **proven**
  (a fact, not a hope).
- `pnk/machinestep.pnk` — the IMPLEMENTATION. `Dec`/`Assign`/`If`/`While`/
  `LoadByte`/`Store` over word ops; the step body is a nested `If` (classify then
  saturate), folded by a `while` over the input stream.
- `pnk/machinestep_ffi.c` — the trusted FFI driver (`@load_vec` parses `$BYTES`,
  a decimal byte list, into the stream buffer and writes `len`; `@report_vec`
  prints the final counter). **Outside** any preservation theorem — see §4.
- `hol-c2/machineStepLinkAScript.sml` — the HOL4 Link A theory: the Lean SPEC
  re-declared, the `stepBody` panLang AST, the `mRel` state relation, and six
  theorems with full proofs. `Holmake` green, `machineStepLinkATheory [1/1] OK`.
- `hol-c2/Holmakefile`, `hol-c2/verify_out.txt` — the build recipe and the
  printed theorem statements + `[oracles]`/`[axioms]` tags.
- `run/machinestep_vectors.txt` — the two-kernel raw runs.

## 3. The emission and the two-kernel agreement (deliverable 1)

Compilation on hbox with the released `cake` (`~/r05/cake-x64-64/cake`):

```
cake --pancake < machinestep.pnk > machinestep.S      # cake_exit=0, 10,089 bytes
cc -O2 machinestep.S basis_ffi.c machinestep_ffi.c -lm -o machinestep   # cc_exit=0
```

The two kernels, nine input streams (`0x7f = 127` is the boundary HOLD byte,
`0x80 = 128` the boundary EVENT byte):

| vector | input bytes | Lean `C2.run` | **compiled Pancake x64** |
|---|---|--:|--:|
| empty         | `[]`                        | 0   | **0** |
| all-low       | `0 127 16 127 0`            | 0   | **0** |
| three-events  | `128 255 129 127 0`         | 3   | **3** |
| boundary-127  | `127 127 127`               | 0   | **0** |
| boundary-128  | `128 128 128`               | 3   | **3** |
| mixed         | `128 0 144 127 160 64 255`  | 4   | **4** |
| **burst-300** | `255 × 300`                 | 255 | **255** |
| burst-255     | `255 × 255`                 | 255 | **255** |
| burst-254     | `255 × 254`                 | 254 | **254** |

Two kernels, one column of answers. The boundary pair (127 holds, 128 fires) is
where an off-by-one in the classify would show; the burst trio is where a missing
saturation (or a `UInt`/word wrap) would show — 300 events must land on `255`, and
both kernels agree it does. This is the C0-style behavioral round-trip, here with
the machine as the second kernel and the HOL4 kernel supplying the single-step
theorem below rather than per-vector `EVAL` (the theorem is universally quantified
over all `c, b`, so it subsumes the vectors).

**Honesty about what §3 is.** Agreement on nine vectors is kernel-checked
*testing*. It is strong evidence but not the refinement theorem. The theorem is §4.

## 4. Link A for the transition, proven (deliverable 2)

`hol-c2/machineStepLinkAScript.sml`, against the **actual** `panSem$evaluate` /
`panSem$eval` of the CakeML tree (CakeML `ed31510b3`, HOL4 Trindemossen 2,
2026-07-02), built green against the real `panSemTheory`.

**The Lean SPEC, re-declared in HOL** (byte-identical to `C2.step` over `num`):
`mstep c b = if b < 128 then c else if c < 255 then c + 1 else 255`.

**The IMPLEMENTATION** `stepBody` — the `.pnk` step body as a real `panLang$prog`
(`Cmp Less` = the SIGNED comparison Pancake `<` compiles to; word literals fixed
to word64):

```
If (Cmp Less (Var Local «b») (Const 128w))
   (Assign Local «c» (Var Local «c»))                         (* hold  *)
   (If (Cmp Less (Var Local «c») (Const 255w))
       (Assign Local «c» (Op Add [Var Local «c»; Const 1w]))  (* advance *)
       (Assign Local «c» (Const 255w)))                       (* saturate *)
```

**The state relation** `mRel c b s`: `s.locals` holds `n2w c` at `«c»` and `n2w b`
at `«b»`, and the sizes fit the non-negative signed range needed by the guards
(`c ≤ 255`, `b < 256`).

| theorem | what it says (all `[oracles: DISK_THM] [axioms: ]`) |
|---|---|
| **`mstep_le`** | `c ≤ 255 ⇒ mstep c b ≤ 255` — the saturation MEANING: the transition never lets the counter exceed the cap. |
| **`signed_lt_n2w64`** | `x,y < 2^63 ⇒ ((n2w x : word64) < n2w y ⇔ x < y)` — the C1 convention lemma, reused verbatim: on the non-negative signed range the SIGNED word order agrees with ℕ order. Discharges both guards (the Pancake `<` is signed). |
| **`eval_class_guard`** | `mRel … ⇒ eval s (Cmp Less (Var «b») (Const 128w)) = SOME (ValWord (if b < 128 then 1w else 0w))` — real `panSem$eval` of the classify guard = `1w` iff the byte is low. |
| **`eval_cap_guard`** | `mRel … ⇒ eval s (Cmp Less (Var «c») (Const 255w)) = SOME (ValWord (if c < 255 then 1w else 0w))` — real `eval` of the saturate guard = `1w` iff the counter is below the cap. |
| **`evaluate_stepBody`** | `mRel … ⇒ evaluate (stepBody, s) = (NONE, set_var «c» (ValWord (n2w (mstep c b))) s)` — **the core**: real `panSem$evaluate` of the emitted step writes EXACTLY the Lean model's next state `n2w (mstep c b)` into `c`. |
| **`stepBody_refines_step`** | `mRel c b s ⇒ ∃s'. evaluate (stepBody, s) = (NONE, s') ∧ FLOOKUP s'.locals «c» = SOME (ValWord (n2w (mstep c b))) ∧ mRel (mstep c b) b s'` — **the headline**: after the emitted step the state local holds the Lean next state AND `mRel` holds again at the new counter. |

The last theorem is the transition-system Link A. Read the third conjunct
`mRel (mstep c b) b s'` carefully: the state relation is an **invariant preserved
by the emitted step**. That is what makes the single step compose into a fold
(the machine can take another step from `s'`), and it is where the saturation
MEANING lands on the machine side — re-establishing `c ≤ 255` for `mstep c b`
requires `mstep_le`, so the theorem literally cannot close without the no-overflow
fact. This constrains **behaviour** (the emitted code computes precisely the Lean
transition), not merely bounds or totality.

**Why this is the generalization asked for.** C1's `evaluate_boundsChk` proves
`evaluate` writes a **constant** (`c0_encode NONE = 0xFFFFFFFF`) on one arm and
does nothing on the other. C2's `evaluate_stepBody` proves `evaluate` writes a
**data-dependent next state `mstep c b`** across three arms, and
`stepBody_refines_step` proves the **state relation is carried forward** —
State → State, not decision → sentinel. Same real-`panSem` machinery
(`eval_def`, `word_cmp_def`, `word_add_n2w`, `set_kvar_def`, the signed-range
lemma), lifted from a one-shot decision to an iterable transition.

## 5. What is inherited, and what is still owed (the honest boundary)

- **Backend (Link B).** Still inherited, unchanged from C0: CakeML's
  `pan_to_target_compile_semantics` (`check_thm`'d in the CakeML tree) deletes
  `cake`'s codegen, `cc`'s optimizer, and `rustc`/`leanc` from the TCB for the
  compiled Pancake. C2 does not re-do it; it is the cited, free half. Instantiating
  it at `stepBody` (checking the `pancake_good_code`/heap side conditions) is a
  checking obligation, not done here.
- **Concrete-syntax → AST faithfulness.** `stepBody` is the `.pnk` step body
  transcribed into the `panLang` AST **by hand**, not derived by running the
  Pancake parser theory (`panPtreeConversion`) on `machinestep.pnk`. Closing that
  (parse the `.pnk`, prove the parser output equals `stepBody`) is the same small,
  named residual C1 carried. That the compiled binary agrees on all nine vectors
  (§3) is independent evidence the transcription is faithful, but it is not a proof.
- **The FFI is unspecified.** `machinestep_ffi.c` (`@load_vec`/`@report_vec`, the
  stream-encoding oracle) sits entirely outside any theorem, exactly as all CakeML
  FFI does.

## 6. The UNCLOSED item: the stream fold `While`

`evaluate_stepBody` is the **single transition**. The whole machine (`C2.run`,
`pnk/machinestep.pnk`) folds the step over the input stream with a `while i < len`
loop. Link A for that fold is **NOT proven here**:

> **UNCLOSED (C2).** `evaluate (machineMain, s)` where `machineMain` is the full
> `.pnk` (the `While` folding `stepBody` and a `LoadByte` per byte) refines
> `C2.run` — i.e. the final counter equals `FOLDL mstep 0 (input bytes)`.

This is a loop-invariant induction over `panSem`'s clocked `While` clause
(invariant `c = FOLDL mstep 0 (TAKE i input) ∧ pos = i ∧ i ≤ len`, induction on
`len − i`) plus the byte-memory relation for the per-iteration `LoadByte` — the
**exact analogue** of C1 §4-A-2/3 (the deferred scan loop + memory relation). It
sits on the now-proven single-step transition, so the loop proof inherits a
working step lemma (`stepBody_refines_step`) as its loop body and owes only the
induction and the memory relation. Estimated cost unchanged from C1: the loop is
the multi-day item; the step around it is done.

## 7. Bottom line — is a SECOND primitive now emitted + preservation-proven?

**Yes, for the single-step obligation, and it is a genuinely different shape.**

- **Region primitive (C0/C1):** emitted, run on 8 vectors, Link A **proven** for
  the bounds **decision** (writes a constant); scan `While` deferred.
- **Machine primitive (C2):** emitted, run on 9 vectors, Link A **proven** for the
  **transition** (writes a data-dependent next state and preserves the state
  relation); fold `While` deferred.

So **2 of the compiler lane's primitive families now have a paid single-step/
single-decision Link A against real `panSem`**, both with the fold/scan loop as the
shared, named, remaining cost. C2 also discharges what EMIT-HOL4-REPORT left as a
**stated obligation** for the machine template (the toggle refinement theorem was
emitted as an unproven comment) — a richer machine primitive now has a real,
kernel-checked transition-refinement theorem, so the machine family is no longer
scaffold-only.

**What full-engine emission still needs**, concretely, after C2:
1. **The fold/stream `While` Link A** (§6) — the dominant, shared per-primitive
   cost (loop-invariant induction + byte-memory relation). This is the one item
   that recurs for every looping primitive and is still unpaid for both families.
2. **Composition** of the single-step theorem into the stream via that `While`
   (the step lemma is the loop body; the induction is what wraps it).
3. **Parser faithfulness** (§5) — parse the `.pnk`, prove the AST equals the
   hand-written `stepBody`/`boundsChk`. Small, named, per-primitive.
4. **Link B instantiation** — discharge the `pancake_good_code`/heap side
   conditions for each emitted program (checking, not new proof).
5. **A whole-program `Dec`/`Store`/FFI story** — the current theorems cover the
   step body in isolation; the full `main` wraps it in `Dec`s, a `Store`, and two
   FFI calls that are outside the theorem (§5). A whole-system claim owes the FFI
   a spec and the `Dec`/`Store` frame their evaluate lemmas.

The unit cost of the verified-compiler goal is now measured on **two** distinct
primitive shapes, not one: the front-end Link A for a stateful transition is the
same order of effort as for a bounds decision (hours, on the proven expression/
word/`set_var` toolkit), and the fold loop is the shared multi-day tail. That —
two families emitted-and-single-step-proven, one loop obligation between them and
full-engine emission — is the honest state after C2.
