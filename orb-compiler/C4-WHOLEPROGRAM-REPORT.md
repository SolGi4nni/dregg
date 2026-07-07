# C4 REPORT — the WHOLE PROGRAM: a small Pancake `main` is now preservation-proven, not just the loop. The Dec/init/Store frame discharges the loop precondition and threads the result to memory

**Date:** 2026-07-03 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**Status: DONE for the whole-program frame — the item C3 §5.1 named UNCLOSED.**
A HOL4 theory (`hol-c4/machineWholeLinkAScript.sml`) builds the emitted `.pnk`
`main` MINUS its two FFI calls as a real `panLang$prog` — the `Dec`s that
initialise `c:=0`, `i:=0`, the proven `machineLoop`, and the `Store` that writes
the counter out — and proves against the REAL `panSem$evaluate` that running it
computes the Lean model's whole-stream result `FOLDL mstep 0 input` (= `C2.run`)
into memory at `base_addr + 24`. Six kernel-checked theorems, every one
`[oracles: DISK_THM] [axioms: ]`, `axioms "machineWholeLinkA" = 0` — no cheats, no
oracles, no extra axioms. Clean from-scratch rebuild: `machineStepLinkATheory
[1/3] OK`, `machineLoopLinkATheory [2/3] OK`, `machineWholeLinkATheory [3/3] OK`.

## Verdict in one paragraph

C3 proved Link A for the LOOP in isolation (`machineLoop_refines_run`): the
emitted `While` computes `FOLDL mstep 0 input` into local `«c»`, **assuming** the
loop precondition `loopInv .. 0 0` (accumulator 0, index 0, `«len»`/`«base»` set,
`memRel` holding). C3 named the residual precisely (§5.1): the WHOLE-PROGRAM FRAME
— establishing `loopInv .. 0 0` from `main`'s `Dec` initialisation, the
`Dec`/`Store`/FFI frame, and linking `memRel` to what the FFI writes. C4
discharges the frame. The headline theorem `mainFrame_refines_run` **composes
C3's loop theorem verbatim**, DISCHARGES its `loopInv .. 0 0` precondition from
the `Dec`-initialised state plus the packaged FFI postcondition, evaluates the
result `Store`, and concludes that the whole small program leaves
`n2w (FOLDL mstep 0 input)` in memory at `base_addr + 24`. What it is **not**: it
does not model the two `ExtCall`s (`@load_vec`, `@report_vec`) inside the theorem
— `@load_vec`'s postcondition is packaged as the hypothesis `loadedRel` and
`@report_vec` only reads the already-written result. So this is `main` with the
FFI boundary replaced by its spec — the honest "main-minus-FFI" the goal
authorised, with the FFI-oracle linkage named as the standing residual.

---

## 1. What was proven (against the real `panSem` / `panProps`)

Theory `machineWholeLinkA`, `Holmake` green as `machineWholeLinkATheory [3/3] OK`
against the just-built `panSemTheory` + `panPropsTheory`, CakeML `ed31510b3`
(2026-06-29), HOL4 `a9846ebe2` (Trindemossen 2, 2026-07-02), Poly/ML 5.9.2. It
**composes C2 and C3**: `machineStepLinkATheory` and `machineLoopLinkATheory` are
build dependencies, and `machineLoop`, `machineLoop_refines_run`, `loopInv`,
`memRel`, `fix_clock_id`, `mstep` are opened and reused unchanged. Full statements
in `hol-c4/verify_out.txt`.

**The emitted whole-program frame** (`mainFrame`, a real `panLang$prog` — the
`.pnk` `main` minus the two `ExtCall`s):
```
Dec «c» One (Const 0w)                                       (* var c = 0   *)
  (Dec «i» One (Const 0w)                                    (* var i = 0   *)
    (Dec «b» One (Const 0w)                                  (* the byte slot *)
      (Seq machineLoop                                       (* the C3 proven loop *)
           (Store (Op Add [BaseAddr; Const 24w])             (* st base+24, c; *)
                  (Var Local «c»)))))
```

**The packaged FFI postcondition** (`loadedRel` — the `@load_vec` spec, ASSUMED):
```
loadedRel input bufAddr s ⇔
  FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input))) ∧
  FLOOKUP s.locals «base» = SOME (ValWord bufAddr) ∧          (* the buffer pointer *)
  memRel input bufAddr s ∧                                    (* the stream in memory *)
  LENGTH input < 2 ** 63 ∧ EVERY (λx. x < 256) input
```

| theorem | what it says (all `[oracles: DISK_THM] [axioms: ]`) |
|---|---|
| **`Dec_zero`** | `evaluate (prog, st with locals := st.locals⟨v↦0w⟩) = (res,st') ⇒ evaluate (Dec v One (Const 0w) prog, st) = (res, st' with locals := res_var st'.locals (v, FLOOKUP st.locals v))` — one initialiser `Dec`: run the body in the extended locals, then restore `v` (memory/clock threaded through unchanged). |
| **`Seq_NONE_le`** | `evaluate (p1,s)=(NONE,sa) ∧ sa.clock≤s.clock ∧ evaluate (p2,sa)=(NONE,sb) ⇒ evaluate (Seq p1 p2, s)=(NONE,sb)` — C3's `Seq_NONE` weakened from `sa.clock=s.clock` to `≤`, which is what the clock-consuming loop needs to sequence with the `Store`. |
| **`evaluate_result_store`** | `FLOOKUP s'.locals «c» = SOME (ValWord w) ∧ (s'.base_addr+24w) ∈ s'.memaddrs ⇒ evaluate (Store (base_addr+24) c, s') = (NONE, s' with memory := s'.memory⦇s'.base_addr+24w ↦ Word w⦈)` — the emitted result `Store` writes `Word w` at `base_addr + 24`, via real `mem_stores`/`mem_store`. |
| **`mainFrame_refines_run`** | **THE WHOLE-PROGRAM Link A** — `loadedRel input bufAddr s ∧ LENGTH input ≤ s.clock ∧ (s.base_addr+24w) ∈ s.memaddrs ⇒ ∃fs. evaluate (mainFrame, s) = (NONE, fs) ∧ fs.memory (s.base_addr+24w) = Word (n2w (FOLDL mstep 0 input))`. |

`FOLDL mstep 0 input` is the HOL twin of the Lean model's `C2.run` (identical to
C3's headline). The conclusion says the whole small program runs to completion
(`NONE` — no error, no `TimeOut`) and the **result word it writes to memory** is
exactly the Lean model's whole-stream answer.

## 2. How the frame discharges the loop precondition (the named C3 residual)

The proof is the composition C3 could not exhibit, done in five moves:

1. **`Dec` initialisation establishes `loopInv .. 0 0`.** The three `Dec`s prepend
   `«c»↦0w`, `«i»↦0w`, `«b»↦0w` to the locals. On the resulting state the proof
   discharges `loopInv input bufAddr 0 0`: the `«c»`/`«i»` fields are `n2w 0`, the
   `«len»`/`«base»` fields survive from `loadedRel` (they are not `«c»`/`«i»`/`«b»`),
   the `«b»` slot exists, and `memRel` transfers because the `Dec`s touch only
   locals (`memRel` depends only on `memory`/`memaddrs`/`be`). **This is the exact
   precondition C3 assumed and named UNCLOSED.**

2. **C3's loop, composed verbatim.** `machineLoop_refines_run` is applied to that
   state, yielding a post-loop state `s'` with `«c» = n2w (FOLDL mstep 0 input)`.
   The `Dec` clock is unchanged (`Dec` does not tick), so the `LENGTH input ≤
   s.clock` hypothesis feeds straight through.

3. **The frame is preserved across the loop.** `panProps`'s `evaluate_invariants`
   (a real-`panSem` frame lemma) gives `s'.base_addr = s.base_addr` and
   `s'.memaddrs = s.memaddrs` — so the result `Store`'s address is computed from
   the same `base_addr` and lands in the same `memaddrs`. `evaluate_clock` gives
   `s'.clock ≤ s.clock`, which is what `Seq_NONE_le` needs.

4. **The result `Store` writes the fold.** `evaluate_result_store` fires with
   `w = n2w (FOLDL mstep 0 input)`: the emitted `Store (base_addr+24) c` writes
   that word to memory.

5. **The three `Dec`s peel back.** Each `Dec` restores its local on exit
   (`res_var`) but leaves memory untouched, so the final state's memory at
   `base_addr + 24` is exactly the fold result — read back with `APPLY_UPDATE_THM`.

No `cheat`, `new_axiom`, or oracle; the footprint audit (`verify_out.txt`) is
clean: `axioms "machineWholeLinkA" = 0`.

## 3. Is a WHOLE small program now preservation-proven? (the honest verdict)

**Yes, for the front-end (Link A), for this primitive, end to end — with the FFI
boundary named.** The theorem is about the *whole* `main` frame (the initialiser
`Dec`s, the loop, and the output `Store`), not the loop in isolation. Three
honest boundaries remain, each named and none of them the loop-induction research
item (that is paid, in C3):

1. **The FFI-oracle linkage (the one substantive residual).** The two `ExtCall`s
   are elided and replaced by their spec. `@load_vec`'s postcondition IS the
   hypothesis `loadedRel` — it asserts the input stream is in the buffer
   (`memRel`), the length is in `«len»`, and the buffer pointer is in `«base»`. A
   full-FFI theorem would model the `ExtCall` node: `read_bytearray` the args,
   `call_FFI s.ffi (ExtCall "load_vec")`, `write_bytearray` the returned bytes,
   and DISCHARGE `loadedRel` (in particular `memRel` at `mem_load_byte`) from what
   the FFI oracle wrote. That is the standing "`memRel` altitude" item C3 §5.2
   named: `memRel` is stated at the byte-read result, not unfolded through
   `write_bytearray`/`get_byte`/endianness to the C `@load_vec` writes. C4 assumes
   `loadedRel`; connecting it to the actual `ExtCall` semantics is the residual.
   `@report_vec` only READS the already-written result word, so it is outside the
   refinement of the computed value.

2. **Parser faithfulness (carried from C1/C2/C3).** `mainFrame`, `machineLoop`,
   `stepBody` are the `.pnk` transcribed into the `panLang` AST by hand, not
   derived by running `panPtreeConversion` on `machinestep.pnk`. Two small naming
   deviations are part of this: the loop's buffer-base local is `«base»` in the C3
   AST but `buf` in the `.pnk` (they denote the same `@base + 32` pointer), and
   `«b»` is pre-declared before the loop rather than `Dec`'d per iteration. The
   compiled binary's agreement on nine vectors (C2 §3) is independent evidence the
   transcription is faithful, but it is not a proof.

3. **Link B instantiation (carried).** See §4.

## 4. What remains for Link B (`pan_to_target`) at the whole-program level

`mainFrame_refines_run` is Link A — the Pancake **source** semantics of the whole
frame computes `C2.run`. To make **leanc leave the TCB end to end** for this
primitive, Link B must be instantiated at `mainFrame`:

- CakeML's `pan_to_target_compile_semantics` (`check_thm`'d in the CakeML tree) is
  the cited, free half: it states that the target machine code the verified
  Pancake backend emits refines the Pancake source `semantics`, deleting `cake`'s
  codegen, `cc`'s optimizer, and `rustc`/`leanc` from the TCB. C4 does **not**
  re-prove it.
- Instantiating it owes: (a) discharging the `pancake_good_code`/heap/well-formed
  side conditions **for `mainFrame`** (a whole-program program now, not just the
  loop body) — a checking obligation, not new proof; and (b) lifting C4's clocked
  `evaluate` theorem to the clock-quantified top-level `semantics` statement (the
  `semantics` wrapper existentially quantifies the clock; C4's `LENGTH input ≤
  s.clock` is the standard "enough fuel" precondition, so this is mechanical).
- The FFI residual (§3.1) sits at the Link-B boundary too: `pan_to_target`'s
  semantics preservation is stated relative to an FFI oracle, so the whole-program
  target claim inherits the same `@load_vec`/`@report_vec` oracle spec that Link A
  assumes. Both halves share exactly one FFI assumption.

So the precise state of **"leanc out of the TCB for this primitive end to end"**:
the front-end whole-program Link A is now CLOSED (the emitted small program's
source semantics computes `C2.run` to memory, kernel-checked, clean footprint);
what stands between that and a full leanc-free target claim is the Link-B
instantiation (checking `pancake_good_code` for `mainFrame` + the mechanical
clock lift, inherited not re-proven) and the single shared FFI-oracle spec
(`@load_vec` writes `loadedRel`). Neither is an open proof-research item; both are
named, bounded, and — for Link B — deliberately not re-done because it is the
cited half of the CakeML tree.

## 5. Files (under `docs/engine/probes/compiler/`)

- `hol-c4/machineWholeLinkAScript.sml` — the theory: `mainFrame`/`loadedRel`, the
  `Dec_zero`/`Seq_NONE_le`/`evaluate_result_store` frame lemmas, and
  `mainFrame_refines_run`. Opens and composes `machineStepLinkATheory` (C2),
  `machineLoopLinkATheory` (C3), and `panPropsTheory` (`evaluate_invariants`,
  `evaluate_clock`).
- `hol-c4/Holmakefile` — `INCLUDES` for the CakeML `pancake`, `pancake/semantics`,
  `compiler/backend`, `compiler/encoders/asm`, `misc`, `semantics/ffi` dirs.
- `hol-c4/verify_out.txt` — the printed theorem statements + `[oracles]`/`[axioms]`
  tags and the `axioms = 0` footprint audit.

## 6. Reproduce

On hbox, with the CakeML tree at `~/src/cakeml` and HOL4 at `~/src/HOL`:
```
export CAKEMLDIR=$HOME/src/cakeml
export PATH=$HOME/src/HOL/bin:$PATH
# work dir must contain: Holmakefile, machineStepLinkAScript.sml (C2),
#                        machineLoopLinkAScript.sml (C3), machineWholeLinkAScript.sml (C4)
cd <workdir> && Holmake machineWholeLinkATheory.uo   # builds C2, C3, then C4, green
```
C2, C3, C4 each compile in ~5 s on hbox after `panSemTheory`/`panPropsTheory` are
built. `verify_out.txt` is regenerated by loading `machineWholeLinkATheory` with
`Globals.show_tags := true`.

## 7. Bottom line for Phase C

C3 paid the per-primitive long pole (the loop-invariant induction over the clocked
`While`). C4 closes what C3 explicitly deferred: the **whole-program frame**. A
whole small program — not just the loop — is now Link-A preservation-proven
against real `panSem`: the emitted `main` frame's `Dec` initialisation establishes
the loop's `loopInv .. 0 0` precondition, C3's loop is composed verbatim, and the
result `Store` threads the Lean model's `C2.run` answer to memory, all with a
clean kernel footprint. What stands between this and a fully leanc-free target
claim for the primitive is the inherited Link-B instantiation (a checking
obligation) and a single FFI-oracle spec (`@load_vec` ⇒ `loadedRel`) — both named,
bounded, and neither an open research item.
